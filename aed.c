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
static bool change;	    /* change flag */
static char lastfile[4096]; /* last edit file */
static size_t marks[26];    /*marks */
static char templ[256];	    /* template main temp file */
static char utempl[256];    /* template undo temp file */
static size_t uendl;	    /* undo end line (last) */
static int fd = -1;	    /* main temp file */
static int ufd = -1;	    /* undo temp file */
static struct timeval tv;   /* for timestamp */

inline static void
tmpclose(int *fd, char *templ)
{
	if (*fd >= 0)
		close(*fd);
	unlink(templ);
	*fd = -1;
}

inline static void
savefile(void)
{
	char buf[65535];
	ssize_t n;

	if (ufd >= 0)
		tmpclose(&ufd, utempl);
	snprintf(utempl, sizeof(utempl), "/tmp/aedundoXXXXXX");
	if ((ufd = mkstemp(utempl)) < 0)
		return;
	uendl = endl;
	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf))))
		if (write(ufd, buf, n) != n)
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

static inline char *
expr(char *s, unsigned long long *n, size_t cur, size_t end)
{
	unsigned long long tmp;
	char *endp = s, c;

	while (*endp == '+' || *endp == '-') {
		c = *endp++;
		s = endp;

		if (*s == '$') {
			tmp = end;
			++endp;
		} else if (*s == '.') {
			tmp = cur;
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
	if (*sp) { /* parse command */
		out->c = *sp;
		if (*(sp + 1)) /* parse argument */
			snprintf(out->arg, sizeof(out->arg), "%s", sp + 1);
	}
	n = sp - s;
	if (n) { /* parse range */
		if (*s == ',' || *s == ';') {
			out->x = (*s == ';') ? cur : 1;
			out->y = end;
			if (n > 1) {
				++s;
				if (*s == '$' || *s == '.') {
					n = (*s == '.') ? cur : end;
					endp = s + 1;
				} else {
					if (*s == '-')
						return 0;
					errno = 0;
					n = strtoull(s, &endp, 10);
					if (errno != 0 || s == endp ||
					    n > SIZE_MAX)
						return 0;
				}
				if (!expr(endp, &n, cur, end))
					return 0;
				out->y = (size_t)n;
			}
		} else {
			if (*s == '$' || *s == '.') {
				n = (*s == '.') ? cur : end;
				endp = s + 1;
			} else {
				if (*s == '-')
					return 0;
				errno = 0;
				n = strtoull(s, &endp, 10);
				if (errno != 0 || s == endp || n > SIZE_MAX)
					return 0;
			}
			if (!(endp = expr(endp, &n, cur, end)))
				return NULL;
			out->y = out->x = (size_t)n;
			if (*endp == ',' || *endp == ';') {
				s = endp + 1;
				if (*s == '$' || *s == '.' ||
				    isdigit((uint8_t)*s)) {
					if (*s == '$' || *s == '.') {
						n = (*s == '.') ? cur : end;
						endp = s + 1;
					} else {
						if (*s == '-')
							return 0;
						errno = 0;
						n = strtoull(s, &endp, 10);
						if (errno != 0 ||
						    n > SIZE_MAX || s == endp)
							return 0;
					}
					if (!expr(endp, &n, cur, end))
						return 0;
					out->y = (size_t)n;
				}
			}
		}
	}

	return 1;
}

static void
quit(int sig)
{
	(void)sig;
	struct timeval tv1, res;
	tmpclose(&fd, templ);
	tmpclose(&ufd, utempl);
	gettimeofday(&tv1, NULL);
	timersub(&tv1, &tv, &res);
	printf("AExit: %ld sec\n", res.tv_sec);
	exit(0);
}

static bool
edit(edcom *c)
{
	char buf[65535];
	ssize_t n, tot = 0;
	int tmpfd;

	if (!c || !*c->arg || !c->arg[1]) {
		if (!*lastfile)
			return 0;
	} else
		snprintf(lastfile, sizeof(lastfile), "%s", c->arg + 1);

	tmpclose(&fd, templ);
	endl = 0;
	snprintf(templ, sizeof(templ), "/tmp/aedXXXXXX");

	if ((fd = mkstemp(templ)) < 0)
		return 0;
	if ((tmpfd = open(lastfile, O_RDONLY)) < 0)
		return 0;
	while ((n = read(tmpfd, buf, sizeof(buf)))) {
		tot += n = write(fd, buf, n);
		while (n--)
			if (buf[n] == '\n')
				++endl;
	}

	close(tmpfd);
	printf("AEdit: %zu [%zu lines]\n", tot, endl);
	curl = endl;
	return 1;
}

static bool
print(edcom *c, bool number, bool list)
{
	ssize_t n, i, k, off, cur = 0;
	char buf[65535];
	bool flag = 0;

	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf)))) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] != '\n')
				continue;
			++cur;
			if (cur == c->x)
				flag = 1;
			if (flag) {
				buf[i] = 0;
				if (number)
					printf("%zu\t", cur);
				if (!list)
					puts(buf + off);
				else {
					for (k = off; k < i + 1; k++) {
						switch (buf[k]) {
						case '\\':
							printf("\\\\");
							break;
						case '\a':
							printf("\\a");
							break;
						case '\n':
							printf("\\n");
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
						case 0:
							printf("\\$\n");
							break;
						default:
							putchar(buf[k]);
							break;
						}
					}
				}
			}
			if (cur == c->y)
				goto ret;
			off = i + 1;
		}
	}
ret:
	curl = c->y;
	return 1;
}

static bool
readfile(edcom *c, bool slient, bool save)
{
	char ntempl[] = "/tmp/aedreadXXXXXX";
	ssize_t n, i, k, tot = 0, off, cur = 0, l = 0;
	char buf[65535], buf1[65535];
	;
	int ifd, tmpfd;
	bool flag = 0;

	if (!*c->arg || !c->arg[1]) {
		if (!*lastfile)
			return 0;
	} else
		snprintf(lastfile, sizeof(lastfile), "%s", c->arg + 1);
	if (save)
		savefile();
	if ((ifd = open(lastfile, O_RDONLY)) < 0)
		return 0;
	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	if (!c->x) {
		while ((n = read(ifd, buf, sizeof(buf)))) {
			if (write(tmpfd, buf, n) != n)
				goto err;
			tot += n;
			while (n--)
				if (buf[n] == '\n')
					++l;
		}
		flag = 1;
	}
	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf)))) {
		off = 0;
		for (i = 0; !flag && i < n; i++) {
			if (buf[i] != '\n')
				continue;
			if (++cur != c->x)
				continue;
			off = i + 1;
			if (write(tmpfd, buf, off) != off)
				goto err;
			while ((k = read(ifd, buf1, sizeof(buf1)))) {
				if (write(tmpfd, buf1, k) != k)
					goto err;
				tot += k;
				while (k--)
					if (buf1[k] == '\n')
						++l;
			}
			flag = 1;
			break;
		}
		if (n > off)
			if (write(tmpfd, buf + off, n - off) != (n - off))
				goto err;
	}
	if (!flag && c->x == endl) {
		while ((n = read(ifd, buf, sizeof(buf)))) {
			if (write(tmpfd, buf, n) != n)
				goto err;
			tot += n;
			while (n--)
				if (buf[n] == '\n')
					++l;
		}
	}

	close(ifd);
	tmpclose(&fd, templ);
	rename(ntempl, templ);
	fd = tmpfd;
	change = 1;
	curl = c->x + l;
	endl += l;

	if (!slient)
		printf("Read: %zu [%zu lines]\n", tot, l);
	return 1;

err:
	close(ifd);
	close(tmpfd);
	unlink(ntempl);
	return 0;
}

static bool
transfer(edcom *c, bool save)
{
	char ntempl[] = "/tmp/aedtransferXXXXXX";
	ssize_t n, i, off, cur = 0;
	unsigned long long post;
	char buf[65535], *endp;
	int tmpfd;
	edcom tmp = { 0 };

	errno = 0;
	post = strtoull(c->arg, &endp, 10);
	if (*c->arg == '-' || errno != 0 || endp == c->arg || post > SIZE_MAX ||
	    post > endl)
		return 0;

	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf)))) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] != '\n')
				continue;
			++cur;
			if (cur >= c->x) {
				if ((write(tmpfd, buf + off, i - off + 1)) <
				    0) {
					close(tmpfd);
					return 0;
				}
			}
			if (cur == c->y)
				goto ret;
			off = i + 1;
		}
	}

ret:
	tmp.x = tmp.y = post;
	snprintf(buf, sizeof(buf), "%s", lastfile);
	snprintf(lastfile, sizeof(lastfile), "%s", ntempl);
	readfile(&tmp, 1, save);
	snprintf(lastfile, sizeof(lastfile), "%s", buf);
	tmpclose(&tmpfd, ntempl);
	return 1;
}

static bool delete(edcom *c, bool save)
{
	char ntempl[] = "/tmp/aeddeleteXXXXXX";
	ssize_t n, i, tot = 0, off, cur = 0;
	char buf[65535];
	int tmpfd;

	if (save)
		savefile();
	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;

	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf)))) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] != '\n')
				continue;
			++cur;
			if ((cur < c->x || cur > c->y)) {
				if ((write(tmpfd, buf + off, i - off + 1)) <
				    0) {
					close(tmpfd);
					return 0;
				}
				++tot;
			}
			off = i + 1;
		}
	}

	tmpclose(&fd, templ);
	rename(ntempl, templ);
	fd = tmpfd;
	endl = tot;
	curl = c->x;
	if (curl > endl)
		curl = endl;
	change = 1;
	return 1;
}

static bool
callunix(edcom *c)
{
	char buf[1024];
	FILE *fp;
	int ret;

	if (!(fp = popen(c->arg, "r")))
		return 0;
	while (fgets(buf, sizeof(buf), fp))
		fputs(buf, stdout);

	ret = pclose(fp);
	puts("!");
	return (ret != -1) ? 1 : 0;
}

static bool
move(edcom *c)
{
	savefile();
	if (!transfer(c, 0))
		return 0;
	if (!delete (c, 0))
		return 0;
	return 1;
}

static bool
writefile(edcom *c)
{
	ssize_t n, i, k, tot = 0, off, cur = 0;
	char buf[65535];
	int tmpfd;

	if ((tmpfd = open(lastfile, O_WRONLY | O_CREAT | O_TRUNC, 0644)) < 0)
		return 0;
	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf)))) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] != '\n')
				continue;
			++cur;
			if (cur >= c->x) {
				if ((k = write(tmpfd, buf + off, i - off + 1)) <
				    0) {
					close(tmpfd);
					return 0;
				}
				tot += k;
			}
			if (cur == c->y)
				goto ret;
			off = i + 1;
		}
	}
ret:
	printf("Write: %zu [%zu lines]\n", tot,
	    (endl > 0) ? cur - c->x + 1 : 0);
	close(tmpfd);
	change = 0;
	return 1;
}

static bool
join(edcom *c)
{
	char ntempl[] = "/tmp/aedjoinXXXXXX";
	ssize_t n, i, tot = 0, off, cur = 0;
	char buf[65535];
	bool flag = 0;
	int tmpfd;

	savefile();
	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;

	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf)))) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] != '\n')
				continue;
			++cur;
			if ((flag = (cur < c->x || cur + 1 > c->y)))
				++tot;
			if ((write(tmpfd, buf + off, i - off + flag)) < 0) {
				close(tmpfd);
				return 0;
			}
			off = i + 1;
		}
	}

	tmpclose(&fd, templ);
	rename(ntempl, templ);
	fd = tmpfd;
	endl = tot;
	curl = c->x;
	change = 1;
	return 1;
}

static bool
validate(edcom *c)
{
	if (c->x == -1 && c->y == -1) {
		switch (c->c) {
		case 'p':
		case 'n':
		case 'l':
		case 'd':
		case 'k':
		case 'm':
		case 't':
			c->x = c->y = curl;
			break;
		case 'r':
		case '=':
			c->x = c->y = endl;
			break;
		case 'j':
			c->x = curl;
			c->y = curl + 1;
		case 'w':
			c->x = 1;
			c->y = endl;
			break;
		}
	}
	switch (c->c) {
	case 'Q':
	case 'E':
	case 'u':
		/* NONE */
		break;
	case '!':
		if (!*c->arg)
			return 0;
		break;
	case 'e':
	case 'q':
		if (change)
			return (change = 0);
		break;

	case 'f':
		if (!*lastfile)
			return 0;
		break;
	case 'p':
	case 'n':
	case 'l':
	case 't':
	case 'j':
	case 'd':
	case 'm':
	case 'w':
		if (fd < 0 || c->y > endl || c->x > endl || c->x > c->y ||
		    c->x <= 0 || c->y <= 0)
			return 0;
		if (c->c == 'w' && endl <= 0)
			return 0;
		break;
	case 'r':
		if (fd < 0 || c->x > endl || c->x < 0)
			return 0;
		break;
	case '=':
		if (c->x > endl || c->x <= 0)
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
		change = 0;
		quit(0);
	case '!':
		return callunix(c);
	case '\'':
		c->x = c->y = marks[tolower(*c->arg) - 'a'];
		return print(c, 0, 0);
	case 'p':
		return print(c, 0, 0);
	case 'j':
		return join(c);
	case 'n':
		return print(c, 1, 0);
	case 'w':
		return writefile(c);
	case 't':
		return transfer(c, 1);
	case 'r':
		return readfile(c, 0, 1);
	case 'd':
		return delete (c, 1);
	case 'm':
		return move(c);
	case '=':
		printf("%zu\n", c->x);
		return 1;
	case 'k':
		marks[tolower(*c->arg) - 'a'] = c->x;
		return 1;
	case 'f':
		puts(lastfile);
		return 1;
	case 'l':
		return print(c, 0, 1);
	case 'e':
		return edit(c);
	case 'E':
		change = 0;
		return edit(c);
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
	gettimeofday(&tv, NULL);
	if (--c) {
		snprintf(lastfile, sizeof(lastfile), "%s", av[1]);
		if (!edit(NULL))
			goto err;
	}
	for (;;) {
		edcom com = { .x = -1, .y = -1, .c = 'p' };
		char buf[65535] = { 0 };
		if (!fgets(buf, sizeof(buf) - 1, stdin))
			goto err;
		buf[strcspn(buf, "\n")] = 0;
		if (!strlen(buf)) /* null command */
			com.y = com.x = curl + 1;
		else if (!parse(buf, curl, endl, &com))
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
