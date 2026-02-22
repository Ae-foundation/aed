/*
 * Copyright (c) 2026, Ae-foundation. All rights reserved.
 *
 * Permission to use, copy, modify, and/or distribute this software for
 * any purpose with or without fee is hereby granted, provided that the
 * software name includes “ae”.
 *
 * THE SOFTWARE IS PROVIDED “AS IS” AND THE AUTHOR DISCLAIMS ALL
 * WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE
 * FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY
 * DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN
 * AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT
 * OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

#include <sys/time.h>

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <regex.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define ASTYLE "\033[1;37m"
#define ARESET "\033[0m"
#define TPLSIZ 256

typedef struct __edcom {
	ssize_t x, y;	/* range */
	char c;		/* command */
	char arg[4096]; /* argument */
} edcom;

static size_t curl;	    /* current line */
static size_t endl;	    /* end line (last) */
static bool cflag;	    /* change flag */
static char lastfile[4096]; /* last edit file */
static size_t marks[26];    /* marks */
static char templ[TPLSIZ];  /* template main temp file */
static char utempl[TPLSIZ]; /* template undo temp file */
static size_t uendl;	    /* undo end line (last) */
static int fd = -1;	    /* main temp file */
static int ufd = -1;	    /* undo temp file */
static time_t tstamp;	    /* for timestamp */
static char tmpbuf[65535];  /* buffer for functions */

inline static char *
expr(char *s, unsigned long long *n, size_t cur, size_t end)
{
	unsigned long long tmp;
	char *endp = s, c;

	while (*endp == '+' || *endp == '-') {
		c = *endp++;
		s = endp;

		if (*s == '$' || *s == '.') {
			tmp = (*s == '$') ? end : cur;
			++endp;
		} else if (isdigit((uint8_t)*s)) {
			errno = 0;
			tmp = strtoull(s, &endp, 10);
			if (errno != 0 || s == endp || tmp > SIZE_MAX)
				return NULL;
		} else
			tmp = 1;

		if (c == '+') {
			if (SIZE_MAX - *n < tmp)
				return NULL;
			*n += tmp;
		} else {
			if (*n < tmp)
				return NULL;
			*n -= tmp;
		}
	}

	return endp;
}

inline static bool
aparse(char *arg, ssize_t *n, size_t cur, size_t end, char **endp)
{
	unsigned long long tmp;
	char *endpt;

	if (*arg == '+' || *arg == '-') {
		tmp = cur;
		endpt = arg;
	} else if (*arg == '$' || *arg == '.') {
		tmp = (*arg == '$') ? end : cur;
		endpt = arg + 1;
	} else {
		errno = 0;
		tmp = strtoull(arg, &endpt, 10);
		if (*arg == '-' || errno != 0 || endpt == arg || tmp > SIZE_MAX)
			return 0;
	}
	if (!(endpt = expr(endpt, &tmp, cur, end)))
		return 0;
	if (tmp > end)
		return 0;
	if (endp)
		*endp = endpt;

	*n = (ssize_t)tmp;
	return 1;
}

static bool
parse(char *s, size_t cur, size_t end, edcom *out)
{
	if (!s || !out)
		return 0;

	unsigned long long n;
	char *sp = s, *endp;

	while (!isalpha((uint8_t)*sp) && *sp != '!' && *sp != '\'' &&
	    *sp != '=' && *sp)
		sp++;
	if (*sp) {
		/* parse command */
		out->c = *sp; /* parse argument  */
		snprintf(out->arg, sizeof(out->arg), "%s",
		    (sp[1]) ? sp + 1 : "");
	}
	if (!(n = sp - s)) /* parse range */
		return 1;
	if (*s == ',' || *s == ';') { /* ,[n] or ;[n] */
		out->x = (*s == ';') ? cur : 1;
		out->y = end;
		if (n > 1 && !aparse(++s, &out->y, cur, end, &endp))
			return 0;
	} else { /* [n], or [n]; or [n],[n] or [n];[n] */
		if (!aparse(s, &out->x, cur, end, &endp))
			return 0;
		out->y = out->x;
		if (*endp != ',' && *endp != ';')
			return 1;
		if (*++endp == '$' || *endp == '.' || isdigit((uint8_t)*endp))
			if (!aparse(endp, &out->y, cur, end, &endp))
				return 0;
	}

	return 1;
}

inline static void
tmpclose(int *fd, char *templ)
{
	if (*fd >= 0)
		close(*fd);
	unlink(templ);
	*fd = -1;
}

inline static void
tmpchange(int *o, char *ot, int *n, char *nt)
{
	tmpclose(o, ot);
	rename(nt, ot);
	*o = *n;
}

inline static bool
setlastfile(char *filename)
{
	while (isspace((uint8_t)*filename))
		++filename;
	if (!*filename) {
		if (!*lastfile)
			return 0;
		return 1;
	}
	snprintf(lastfile, sizeof(lastfile), "%s", filename);
	return 1;
}

inline static void
update(size_t _curl, size_t _endl, bool _cflag)
{
	curl = _curl;
	endl = _endl;
	cflag = _cflag;
}

inline static ssize_t
WRITE(int fd, const void *buf, size_t len)
{
	const char *p = buf;
	size_t left = len;
	ssize_t n;

	while (left) {
		n = write(fd, p, left);
		if (n <= 0) {
			if (n < 0 && errno == EINTR)
				continue;
			return -1;
		}
		left -= n;
		p += n;
	}

	return len;
}

inline static ssize_t
READ(int fd, void *buf, size_t len)
{
	ssize_t n;
	while ((n = read(fd, buf, len)) < 0)
		if (errno != EINTR)
			return -1;
	return n;
}

inline static ssize_t
GETLINE(char **linep, int fd)
{
	ssize_t i = 0, n;
	uint8_t c;

	*linep = NULL;
	while ((n = READ(fd, &c, 1)) > 0) {
		*linep = realloc(*linep, i + 2);
		(*linep)[i++] = c;
		if (c == '\n')
			break;
	}
	if (n < 0)
		return -1;
	if (i > 0)
		(*linep)[i] = 0;

	return i;
}

inline static ssize_t
GETLINERG(size_t x, size_t y, size_t *cur, char **linep, int fd)
{
	ssize_t n;
	char *lp;
	while ((n = GETLINE(&lp, fd)) > 0) {
		/* 01 = 11, 10 = 11, 00 = 11 */
		if (++(*cur) < x || *cur > y) {
			free(lp);
			continue;
		}
		*linep = lp;
		break;
	}
	return n;
}

inline static bool
WRITEFILE(size_t x, size_t y, int *dst, size_t *bytes, size_t *lines)
{
	size_t i = 0, tot = 0, nl = 0;
	ssize_t n;
	char *lp;

	lseek(fd, 0, SEEK_SET);
	while ((n = GETLINERG(x, y, &i, &lp, fd)) > 0) {
		if ((n = WRITE(*dst, lp, n)) < 0) {
			free(lp);
			return 0;
		}
		free(lp);
		tot += n;
		++nl;
	}
	if (n < 0)
		return 0;
	if (lines)
		*lines += nl;
	if (bytes)
		*bytes += tot;

	return 1;
}

inline static bool
READFILE(size_t x, int *src, size_t *bytes, size_t *lines)
{
	char ntempl[] = "/tmp/aedXXXXXX";
	int tmpfd;
	ssize_t n;

	if ((tmpfd = mkstemp(ntempl)) < 0)
		goto err;
	if (x > 0 && !WRITEFILE(1, x, &tmpfd, NULL, NULL))
		goto err;
	lseek(*src, 0, SEEK_SET);
	while ((n = READ(*src, tmpbuf, sizeof(tmpbuf))) > 0) {
		if (WRITE(tmpfd, tmpbuf, n) < 0)
			goto err;
		if (bytes)
			*bytes += n;
		while (lines && n--)
			if (tmpbuf[n] == '\n')
				++*lines;
	}
	if (n < 0)
		goto err;
	if (x < endl && !WRITEFILE(x + 1, endl, &tmpfd, NULL, NULL))
		goto err;

	tmpchange(&fd, templ, &tmpfd, ntempl);
	return 1;
err:
	tmpclose(&tmpfd, ntempl);
	return 0;
}

inline static void
savefile(void)
{
	tmpclose(&ufd, utempl);
	snprintf(utempl, sizeof(utempl), "/tmp/aedXXXXXX");
	if ((ufd = mkstemp(utempl)) < 0)
		return;
	uendl = endl;
	if (!WRITEFILE(1, endl, &ufd, NULL, NULL))
		return tmpclose(&ufd, utempl);
}

static void
undo(void)
{
	if (ufd < 0)
		return;
	char save2[sizeof(templ)];
	size_t save1 = endl;
	int save = fd;
	strcpy(save2, templ);
	fd = ufd;
	ufd = save;
	endl = uendl;
	uendl = save1;
	strcpy(templ, utempl);
	strcpy(utempl, save2);
}

static void
quit(int sig)
{
	(void)sig;
	tmpclose(&fd, templ);
	tmpclose(&ufd, utempl);
	printf("AExit: %ld sec\n", time(NULL) - tstamp);
	exit(0);
}

static bool
print(size_t x, size_t y, bool number, bool list)
{
	char *lp, *esc = "\\\a\t\b\f\r\v", *cp;
	ssize_t n, k;
	size_t i = 0;

	lseek(fd, 0, SEEK_SET);
	while ((n = GETLINERG(x, y, &i, &lp, fd)) > 0) {
		if (number)
			printf("%s%zu%s\t", ASTYLE, i, ARESET);
		for (k = 0; k < n; k++) {
			if (!list)
				putchar(lp[k]);
			else if (lp[k] == '\n')
				puts("$");
			else if ((cp = index(esc, lp[k])))
				printf("\\%c", "\\atbfrv"[cp - esc]);
			else if (isprint((uint8_t)lp[k]))
				putchar(lp[k]);
			else
				printf("\\%03x", (uint8_t)lp[k]);
		}
		free(lp);
	}
	if (n < 0)
		return 0;

	update(y, endl, cflag);
	return 1;
}

static bool
edit(char *filename)
{
	size_t bytes = 0;
	uint8_t l;
	ssize_t n;
	int tmpfd;

	if (!setlastfile(filename))
		return 0;

	if ((tmpfd = open(lastfile, O_RDONLY | O_CREAT, 0644)) < 0)
		return 0;
	endl = 0;
	tmpclose(&fd, templ);
	snprintf(templ, sizeof(templ), "/tmp/aedXXXXXX");
	if ((fd = mkstemp(templ)) < 0)
		goto err;
	if (!READFILE(0, &tmpfd, &bytes, &endl))
		goto err;
	if (bytes > 0) {
		if (lseek(tmpfd, -1, SEEK_CUR) < 0)
			goto err;
		if ((n = READ(tmpfd, &l, 1)) < 0)
			goto err;
		if (n == 1 && l != '\n') { /* last line \n */
			++endl;
			if (WRITE(fd, "\n", 1) < 0)
				goto err;
		}
	}

	close(tmpfd);
	printf("AEdit: %zu [%zu lines]\n", bytes, endl);
	update(endl, endl, cflag);
	return 1;
err:
	close(tmpfd);
	tmpclose(&fd, templ);
	return 0;
}

static bool
writefile(char *filename, size_t x, size_t y)
{
	size_t bytes = 0, nl = 0;
	int tmpfd;
	bool ret;

	if (!setlastfile(filename))
		return 0;
	if ((tmpfd = open(lastfile, O_WRONLY | O_CREAT | O_TRUNC, 0644)) < 0)
		return 0;
	if (!(ret = WRITEFILE(x, y, &tmpfd, &bytes, &nl)))
		printf("FAILED: ");

	close(tmpfd);
	printf("Write: %zd [%zu lines]\n", bytes, nl);
	update(curl, endl, (ret) ? 0 : cflag);
	return ret;
}

static bool
readfile(char *arg, size_t x)
{
	size_t bytes = 0, nl = 0;
	bool ret;
	int ifd;

	if (!setlastfile(arg))
		return 0;
	if ((ifd = open(lastfile, O_RDONLY)) < 0)
		return 0;
	if (!(ret = READFILE(x, &ifd, &bytes, &nl)))
		printf("FAILED: ");

	close(ifd);
	printf("Read: %zu [%zu lines]\n", bytes, nl);
	update((x + nl) ? x + nl : 1, endl + nl, nl);
	return ret;
}

static bool delete(size_t x, size_t y)
{
	char ntempl[] = "/tmp/aedXXXXXX";
	size_t nl = 0;
	int tmpfd;

	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	if (x > 1 && !WRITEFILE(1, x - 1, &tmpfd, NULL, &nl))
		goto err;
	if (!WRITEFILE(y + 1, endl, &tmpfd, NULL, &nl))
		goto err;

	tmpchange(&fd, templ, &tmpfd, ntempl);
	update((x > nl) ? nl : x, nl, 1);
	return 1;
err:
	tmpclose(&tmpfd, ntempl);
	return 0;
}

static bool
transfer(size_t post, size_t x, size_t y)
{
	char ntempl[] = "/tmp/aedXXXXXX";
	size_t nl = 0;
	int tmpfd;

	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	if (!WRITEFILE(x, y, &tmpfd, NULL, NULL))
		goto err;
	if (!READFILE(post, &tmpfd, NULL, &nl))
		goto err;

	tmpclose(&tmpfd, ntempl);
	update(post + nl, endl + nl, 1);
	return 1;
err:
	tmpclose(&tmpfd, ntempl);
	return 0;
}

static int stop = 0;
static void
onsig(int s)
{
	stop = 1;
}

static bool
callunix(char *arg)
{
	void (*save)(int);
	FILE *fp;

	if (!(fp = popen(arg, "r")))
		return 0;
	stop = 0;
	save = signal(SIGINT, onsig);
	while (!stop && fgets(tmpbuf, sizeof(tmpbuf), fp))
		fputs(tmpbuf, stdout);

	puts("!");
	pclose(fp);
	signal(SIGINT, save);
	return !stop;
}

static bool
append(size_t x, bool insert)
{
	char ntempl[] = "/tmp/aedXXXXXX";
	size_t nl = 0, n;
	int tmpfd;

	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	for (;;) {
		if (!fgets(tmpbuf, sizeof(tmpbuf) - 1, stdin)) {
		err:
			tmpclose(&tmpfd, ntempl);
			return 0;
		}
		if (tmpbuf[0] == '.' && tmpbuf[1] == '\n' && tmpbuf[2] == 0)
			break;
		if ((WRITE(tmpfd, tmpbuf, strlen(tmpbuf))) < 0)
			goto err;
	}
	n = x - (insert && x);
	READFILE(n, &tmpfd, NULL, &nl);

	tmpclose(&tmpfd, ntempl);
	update(!(n + nl) && endl ? 1 : n + nl, endl + nl, nl);
	return 1;
}

static bool
join(size_t x, size_t y)
{
	char ntempl[] = "/tmp/aedXXXXXX", *lp;
	size_t i = 0, nl = 0;
	bool flag = 0;
	ssize_t n;
	int tmpfd;

	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	lseek(fd, 0, SEEK_SET);
	while ((n = GETLINE(&lp, fd)) > 0) {
		nl += !(flag = (++i >= x && i < y));
		if ((WRITE(tmpfd, lp, n - flag)) < 0) {
		err:
			tmpclose(&tmpfd, ntempl);
			return 0;
		}
		free(lp);
	}
	if (n < 0)
		goto err;

	tmpchange(&fd, templ, &tmpfd, ntempl);
	update(x, nl, (endl > nl));
	return 1;
}

static char *
aregex(const char *s, const char *re, const char *repl, uint32_t flags)
{
#define GFLAG (1 << 1)
#define LFLAG (1 << 2)
#define NFLAG (1 << 3)
	regmatch_t m;
	regex_t rx;
	if (regcomp(&rx, re, 0) != 0)
		return NULL;
	size_t len = 0, rlen = strlen(repl);
	char *res = NULL, *tmp;
	int eflags = 0;

	while (!regexec(&rx, s, 1, &m, eflags)) {
		if (!(tmp = realloc(res, len + m.rm_so + rlen + 1))) {
			free(res);
			regfree(&rx);
			return NULL;
		}
		memcpy((res = tmp) + len, s, m.rm_so);
		memcpy(res + (len += m.rm_so), repl, rlen);
		len += rlen;
		s += m.rm_eo;
		if (!(flags & GFLAG))
			break;
		if (m.rm_so == m.rm_eo && *s)
			s++;
		if (m.rm_so == m.rm_eo && !*s)
			break;
		eflags = REG_NOTBOL;
	}
	if (res) {
		res = realloc(res, len + strlen(s) + 1);
		strcpy(res + len, s);
	}

	regfree(&rx);
	return res;
}

inline static int
sparse(char *s, char **p)
{
	char *dst = s;
	int n = 0;

	p[n++] = dst;
	while (*s) {
		if (*s == '\\' && s[1] == '/' && s[2] == '/') {
			s++;
			*dst++ = *s++;
		} else if (*s == '/' && n < 3) {
			*dst = 0;
			s++;
			dst = s;
			p[n++] = dst;
		} else
			*dst++ = *s++;
	}

	*dst = 0;
	return n;
}

static bool
substitute(char *arg, size_t x, size_t y)
{
	char ntempl[] = "/tmp/aedXXXXXX";
	size_t nl = 0, i = 0;
	char *res, *lp, *p[3];
	uint32_t flags = 0;
	int tmpfd;
	ssize_t n;

	if ((n = sparse(arg, p)) < 2)
		return 0;
	while (n == 3 && *p[2]) {
		switch (*p[2]++) {
		case 'g':
			flags |= GFLAG;
			break;
		case 'l':
			flags |= LFLAG;
			break;
		case 'n':
			flags |= NFLAG;
			break;
		}
	}

	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	lseek(fd, 0, SEEK_SET);
	while ((n = GETLINE(&lp, fd)) > 0) {
		res = NULL;
		if (++i >= x && i <= y) {
			lp[n - 1] = 0;
			res = aregex(lp, p[0], p[1], flags);
		}
		if (res) {
			if (!WRITE(tmpfd, res, strlen(res)) ||
			    !WRITE(tmpfd, "\n", 1))
				goto err;
			nl = i;
			free(res);
		} else {
			lp[n - 1] = '\n'; /* return */
			if (!WRITE(tmpfd, lp, n))
				goto err;
		}
		free(lp);
	}
	if (n < 0 || !nl)
		goto err;

	tmpchange(&fd, templ, &tmpfd, ntempl);
	if (flags & LFLAG)
		print(nl, nl, 0, 1);
	if (flags & NFLAG)
		print(nl, nl, 1, 0);
	print(nl, nl, 0, 0);

	update(nl, endl, 1);
	return 1;
err:
	if (lp)
		free(lp);
	if (res)
		free(res);
	tmpclose(&tmpfd, ntempl);
	return 0;
}

static bool
validate(edcom *c)
{
	if (c->x == -1 && c->y == -1) {
		switch (c->c) {
		case 'r':
		case '=':
			c->x = c->y = endl;
			break;
		case 'j':
			c->x = curl;
			c->y = curl + 1;
			break;
		case 'w':
			c->x = 1;
			c->y = (endl > 0) ? endl : 1;
			break;
		default:
			c->x = c->y = curl;
			break;
		}
	}
	switch (c->c) {
	case '!':
		if (!*c->arg)
			return 0;
		break;
	case 'e':
	case 'q':
		if (cflag)
			return (cflag = 0);
		break;
	case 'f':
		if (!*lastfile)
			return 0;
		break;
	case 'u':
		if (ufd < 0)
			return 0;
		break;
	case 'p':
	case 'n':
	case 'l':
	case 'j':
	case 'd':
	case 'c':
	case 'w':
	case 'm':
	case 't':
	case 's':
		if (fd < 0 || c->x > c->y || c->x <= 0 || c->y <= 0)
			return 0;
		if (c->c != 'w' && endl <= 0)
			return 0;
		if ((c->c == 'm' || c->c == 't' || c->c == 's') && !*c->arg)
			return 0;
		break;
	case 'r':
	case 'a':
	case 'i':
		if (fd < 0 || c->x < 0)
			return 0;
		break;
	case 'k':
	case '\'':
		if (!isalpha((uint8_t)*c->arg))
			return 0;
		break;
	}

	return 1;
}

static bool
command(edcom *c)
{
	switch (c->c) {
	case 'q':
		quit(0);
	case 'Q':
		cflag = 0;
		quit(0);
	case 's':
		savefile();
		return substitute(c->arg + 1, c->x, c->y);
	case '!':
		return callunix(c->arg);
	case '\'':
		c->x = c->y = marks[tolower(*c->arg) - 'a'];
		return print(c->x, c->y, 1, 0);
	case 'j':
		savefile();
		return join(c->x, c->y);
	case 'a':
	case 'i':
		savefile();
		return append(c->x, (c->c == 'i'));
	case 'c': {
		bool ins = c->y < endl;
		savefile();
		if (!delete (c->x, c->y))
			return 0;
		return append(curl, ins);
	}
	case 'n':
	case 'l':
	case 'p':
		return print(c->x, c->y, (c->c == 'n'), (c->c == 'l'));
	case 'w':
		return writefile(c->arg, c->x, c->y);
	case 't': {
		ssize_t n;
		if (!aparse(c->arg, &n, curl, endl, NULL))
			return 0;
		savefile();
		return transfer(n, c->x, c->y);
	}
	case 'r':
		savefile();
		return readfile(c->arg, c->x);
	case 'd':
		savefile();
		return delete (c->x, c->y);
	case 'm': {
		ssize_t n;
		if (!aparse(c->arg, &n, curl, endl, NULL))
			return 0;
		if (n >= c->x - 1 && n <= c->y)
			return 1;
		size_t off = (n < c->x) ? (c->y - c->x + 1) : 0;
		savefile();
		if (!transfer(n, c->x, c->y))
			return 0;
		return delete (c->x + off, c->y + off);
	}
	case '=':
		printf("%zu\n", c->x);
		return 1;
	case 'k':
		marks[tolower(*c->arg) - 'a'] = c->x;
		return 1;
	case 'f':
		printf("%s", lastfile);
		if (*templ)
			printf(" [%s]", templ);
		putchar('\n');
		return 1;
	case 'e':
		return edit(c->arg);
	case 'E':
		cflag = 0;
		return edit(c->arg);
	case 'u':
		undo();
		return 1;
	}
	return 0;
}

int
main(int c, char **av)
{
	tstamp = time(NULL);
	signal(SIGINT, quit);
	if (--c)
		if (!edit(av[1]))
			goto err;
	for (;;) {
		edcom com = { .x = -1, .y = -1, .c = 'p' };
		if (!fgets(tmpbuf, sizeof(tmpbuf) - 1, stdin))
			goto err;
		tmpbuf[strcspn(tmpbuf, "\n")] = 0;
		if (!strlen(tmpbuf)) /* null command */
			com.y = com.x = curl + 1;
		else if (!parse(tmpbuf, curl, endl, &com))
			goto err;
		if (!validate(&com))
			goto err;
		if (!command(&com))
			goto err;
		continue;
	err:
		puts("?");
	}
	/* NOTREACHED */
	return 0;
}
