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

typedef struct __edcom {
	ssize_t x, y;	/* range */
	char c;		/* command */
	char arg[4096]; /* argument */
} edcom;

static size_t curl;	    /* current line */
static size_t endl;	    /* end line (last) */
static bool cflag;	    /* change flag */
static char lastfile[4096]; /* last edit file */
static size_t marks[26];    /*marks */
static char templ[256];	    /* template main temp file */
static char utempl[256];    /* template undo temp file */
static size_t uendl;	    /* undo end line (last) */
static int fd = -1;	    /* main temp file */
static int ufd = -1;	    /* undo temp file */
static time_t tstamp;	    /* for timestamp */

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

	if (*arg == '$' || *arg == '.') {
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
	if (*sp) {	      /* parse command */
		out->c = *sp; /* parse argument */
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
	if (!*filename || !filename[1]) {
		if (!*lastfile)
			return 0;
		return 1;
	}
	snprintf(lastfile, sizeof(lastfile), "%s", filename);
	return 1;
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

static bool
WRITEFILE(size_t x, size_t y, int *dst, size_t *bytes, size_t *lines)
{
	char buf[65535];
	ssize_t n, i, off;
	size_t cur = 1;

	lseek(fd, 0, SEEK_SET);
	while ((n = READ(fd, buf, sizeof(buf))) > 0) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] == '\n') {
				if (cur >= x && cur <= y) {
					if (WRITE(*dst, buf + off,
						i - off + 1) < 0)
						return 0;
					if (bytes)
						*bytes += i - off + 1;
					if (lines)
						++*lines;
				}
				++cur;
				off = i + 1;
				if (cur > y)
					return 1;
			}
		}
		if (cur >= x && cur <= y && n > off) {
			if (WRITE(*dst, buf + off, n - off) < 0)
				return 0;
			if (bytes)
				*bytes += n - off;
		}
	}
	if (n < 0)
		return 0;

	return 1;
}

static bool
READFILE(size_t x, int *src, size_t *bytes, size_t *lines)
{
	char ntempl[] = "/tmp/aedXXXXXX";
	char buf[65535];
	int tmpfd;
	ssize_t n;

	if ((tmpfd = mkstemp(ntempl)) < 0)
		goto err;

	if (x > 0)
		if (!WRITEFILE(1, x, &tmpfd, NULL, NULL))
			goto err;
	lseek(*src, 0, SEEK_SET);
	while ((n = READ(*src, buf, sizeof(buf))) > 0) {
		if (WRITE(tmpfd, buf, n) < 0)
			goto err;
		if (bytes)
			*bytes += n;
		while (n--)
			if (buf[n] == '\n' && lines)
				++*lines;
	}
	if (n < 0)
		goto err;
	if (x < endl)
		if (!WRITEFILE(x + 1, endl, &tmpfd, NULL, NULL))
			goto err;

	tmpchange(&fd, templ, &tmpfd, ntempl);
	return 1;
err:
	tmpclose(&tmpfd, ntempl);
	return 0;
}

static void
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
	char buf[65535];
	size_t cur = 0;
	bool flag = 1;
	ssize_t n, i;

	lseek(fd, 0, SEEK_SET);
	while ((n = READ(fd, buf, sizeof(buf))) > 0) {
		for (i = 0; i < n; i++) {
			if (flag) {
				if (++cur > y)
					goto ret;
				if (cur >= x && number)
					printf("%zu\t", cur);
				flag = 0;
			}
			if (cur >= x) {
				if (!list) {
					putchar(buf[i]);
				} else {
					switch (buf[i]) {
					case '\\':
						printf("\\\\");
						break;
					case '\a':
						printf("\\a");
						break;
					case '\n':
						puts("$");
						break;
					case '\t':
						printf("\\t");
						break;
					case '\b':
						printf("\\b");
						break;
					case '\f':
						printf("\\f");
						break;
					case '\r':
						printf("\\r");
						break;
					case '\v':
						printf("\\v");
						break;
					default:
						if (isprint((uint8_t)buf[i]))
							putchar(buf[i]);
						else
							printf("\\%03x",
							    (uint8_t)buf[i]);
						break;
					}
				}
			}
			if (buf[i] == '\n')
				flag = 1;
		}
	}
	if (n < 0)
		return 0;
ret:
	if (cur)
		curl = (cur > y) ? y : cur;
	return 1;
}

static bool
edit(char *filename)
{
	uint8_t l;
	size_t tot = 0;
	ssize_t n;
	int tmpfd;

	if (!setlastfile(filename))
		return 0;

	if ((tmpfd = open(lastfile, O_RDONLY | O_CREAT, 0644)) < 0)
		return 0;
	endl = 0;
	tmpclose(&fd, templ);
	snprintf(templ, sizeof(templ), "/tmp/aedXXXXXX");
	if ((fd = mkstemp(templ)) < 0) {
		close(tmpfd);
		return 0;
	}
	if (!READFILE(0, &tmpfd, &tot, &endl))
		goto err;
	if (tot > 0) {
		if (lseek(tmpfd, -1, SEEK_CUR) == -1)
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
	curl = endl;

	printf("AEdit: %zu [%zu lines]\n", tot, endl);
	return 1;
err:
	close(tmpfd);
	tmpclose(&fd, templ);
	return 0;
}

static bool
writefile(char *filename, size_t x, size_t y)
{
	size_t nl = 0, tot = 0;
	int tmpfd;
	bool ret;

	if (!setlastfile(filename))
		return 0;
	if ((tmpfd = open(lastfile, O_WRONLY | O_CREAT | O_TRUNC, 0644)) < 0)
		return 0;
	if ((ret = WRITEFILE(x, y, &tmpfd, &tot, &nl)))
		cflag = 0;
	else
		printf("FAILED: ");

	printf("Write: %zd [%zu lines]\n", tot, nl);
	close(tmpfd);
	return ret;
}

static bool
readfile(char *arg, size_t x)
{
	size_t tot = 0, nl = 0;
	bool ret;
	int ifd;

	if (!setlastfile(arg))
		return 0;
	if ((ifd = open(lastfile, O_RDONLY)) < 0)
		return 0;
	if (!(ret = READFILE(x, &ifd, &tot, &nl)))
		printf("FAILED: ");
	close(ifd);
	curl = x + nl;
	endl += nl;
	cflag = 1;

	printf("Read: %zu [%zu lines]\n", tot, nl);
	return ret;
}

static bool delete(size_t x, size_t y)
{
	char ntempl[] = "/tmp/aedXXXXXX";
	size_t nl = 0;
	int tmpfd;

	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	if (!WRITEFILE(1, x - 1, &tmpfd, NULL, &nl))
		goto err;
	if (!WRITEFILE(y + 1, endl, &tmpfd, NULL, &nl))
		goto err;

	tmpchange(&fd, templ, &tmpfd, ntempl);
	endl = nl;
	curl = (x > endl) ? endl : x;
	cflag = 1;
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

	endl += nl;
	curl = post + nl;
	tmpclose(&tmpfd, ntempl);
	cflag = 1;
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
	char buf[65535];
	void (*save)(int);
	FILE *fp;

	if (!(fp = popen(arg, "r")))
		return 0;
	stop = 0;
	save = signal(SIGINT, onsig);
	while (!stop && fgets(buf, sizeof(buf), fp))
		fputs(buf, stdout);
	puts("!");
	pclose(fp);

	signal(SIGINT, save);
	return !stop;
}

static bool
append(size_t x, bool insert)
{
	char ntempl[] = "/tmp/aedXXXXXX";
	char buf[65535] = { 0 };
	size_t nl = 0;
	int tmpfd;
	ssize_t n;

	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	for (;;) {
		if (!fgets(buf, sizeof(buf) - 1, stdin))
			return 0;
		if (buf[0] == '.' && buf[1] == '\n' && buf[2] == 0)
			break;
		if ((WRITE(tmpfd, buf, strlen(buf))) < 0) {
			tmpclose(&tmpfd, ntempl);
			return 0;
		}
	}

	n = x - ((insert && x != 0) ? 1 : 0);
	READFILE(n, &tmpfd, NULL, &nl);
	tmpclose(&tmpfd, ntempl);

	curl = n + nl;
	endl += nl;
	cflag = 1;
	return 1;
}

static bool
join(size_t x, size_t y)
{
	char ntempl[] = "/tmp/aedXXXXXX";
	ssize_t n, i, tot = 0, off, cur = 0;
	char buf[65535];
	bool flag = 0;
	int tmpfd;

	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;

	lseek(fd, 0, SEEK_SET);
	while ((n = READ(fd, buf, sizeof(buf))) > 0) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] != '\n')
				continue;
			++cur;
			flag = (cur < x || cur >= y);
			if ((WRITE(tmpfd, buf + off, i - off + flag)) < 0) {
			err:
				tmpclose(&tmpfd, ntempl);
				return 0;
			}
			tot += flag;
			off = i + 1;
		}
		if (off < n)
			if ((WRITE(tmpfd, buf + off, n - off)) < 0)
				goto err;
	}
	if (n < 0)
		goto err;

	tmpchange(&fd, templ, &tmpfd, ntempl);
	endl = tot;
	curl = x;
	cflag = 1;
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
	char ntempl1[] = "/tmp/aedXXXXXX";
	char ntempl[] = "/tmp/aedXXXXXX";
	char buf[65535], *res, *bp, *np;
	bool skip = 0, flag = 0;
	uint32_t flags = 0;
	int tmpfd, tmpfd1;
	size_t nl = 0, tot = 1, cur = 0;
	char *p[3];
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
	if (!WRITEFILE(x, y, &tmpfd, NULL, NULL))
		goto err;
	if ((tmpfd1 = mkstemp(ntempl1)) < 0)
		goto err;

	lseek(tmpfd, 0, SEEK_SET);
	while ((n = READ(tmpfd, buf, sizeof(buf) - 1)) > 0) {
		bp = buf;
		buf[n] = 0;
		while (bp < buf + n) {
			if ((np = index(bp, '\n')))
				*np = 0;
			res = (!skip || (flags & GFLAG)) ?
			    aregex(bp, p[0], p[1], flags) :
			    NULL;
			if (res) {
				if (!WRITE(tmpfd1, res, strlen(res)))
					goto err;
				free(res);
				skip = flag = 1;
				cur = tot;
			} else if (*bp && !WRITE(tmpfd1, bp, strlen(bp)))
				goto err;
			if (np) {
				if (!WRITE(tmpfd1, "\n", 1))
					goto err;
				bp = np + 1;
				skip = 0;
				++tot;
			} else
				break;
		}
	}

	if (n < 0 || !flag)
		goto err;
	if (!delete (x, y))
		goto err;
	if (!READFILE(x - 1, &tmpfd1, NULL, &nl))
		goto err;

	tmpclose(&tmpfd, ntempl);
	tmpclose(&tmpfd1, ntempl1);

	endl += nl;
	curl = x - 1 + cur;
	cflag = 1;

	if (flags & LFLAG)
		print(curl, curl, 0, 1);
	if (flags & NFLAG)
		print(curl, curl, 1, 0);
	print(curl, curl, 0, 0);
	return 1;
err:
	tmpclose(&tmpfd1, ntempl1);
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
	signal(SIGINT, quit);
	tstamp = time(NULL);

	if (--c) /* aed [file] */
		if (!edit(av[1]))
			goto error;
	for (;;) { /* main ed loop */
		edcom com = { .x = -1, .y = -1, .c = 'p' };
		char buf[65535] = { 0 };

		if (!fgets(buf, sizeof(buf) - 1, stdin))
			goto error;
		buf[strcspn(buf, "\n")] = 0;

		if (!strlen(buf)) /* null command */
			com.y = com.x = curl + 1;
		else if (!parse(buf, curl, endl, &com))
			goto error;
		if (!validate(&com))
			goto error;
		if (!command(&com))
			goto error;

		continue;
	error:
		puts("?");
	}

	/* NOTREACHED */
	return 0;
}
