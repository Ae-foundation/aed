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
#include <unistd.h>

typedef struct __edcom {
	ssize_t x, y;	/* range */
	char c;		/* command */
	char arg[4096]; /* argument */
} edcom;

static size_t curl;	     /* current line */
static size_t endl;	     /* end line (last) */
static bool change;	     /* change flag */
static char lastfile[65535]; /* last edit file */
static size_t marks[26];     /*marks */
static char templ[256];	     /* template main temp file */
static char utempl[256];     /* template undo temp file */
static size_t uendl;	     /* undo end line (last) */
static int fd = -1;	     /* main temp file */
static int ufd = -1;	     /* undo temp file */

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

inline static void
undo(void)
{
	if (ufd < 0)
		return;

	int save = fd;
	size_t save1 = endl;
	char save3[sizeof(templ)];
	strcpy(save3, templ);

	fd = ufd;
	ufd = save;
	endl = uendl;
	uendl = save1;
	strcpy(templ, utempl);
	strcpy(utempl, save3);
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

inline static void
quit(int sig)
{
	(void)sig;
	tmpclose(&fd, templ);
	tmpclose(&ufd, utempl);
	puts("AExit");
	exit(0);
}

static bool
edit(edcom *com)
{
	char buf[65535];
	ssize_t n, tot = 0;
	int tmpfd;

	if (change)
		return (change = 0);
	if (!*lastfile) {
		if (!com || !strlen(com->arg + 1))
			return 0;
		snprintf(lastfile, sizeof(lastfile), "%s", com->arg + 1);
	}

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
print(edcom *com, bool number, bool list)
{
	ssize_t n, i, k, off, cur = 0;
	char buf[65535];
	bool flag = 0;

	if (fd < 0 || com->y > endl || com->x > endl || com->x > com->y ||
	    com->x <= 0 || com->y <= 0)
		return 0;
	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf)))) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] != '\n')
				continue;
			++cur;
			if (cur == com->x)
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
			if (cur == com->y)
				goto ret;
			off = i + 1;
		}
	}
ret:
	curl = com->y;
	return 1;
}

static bool delete(edcom *com)
{
	char ntempl[] = "/tmp/aeddeleteXXXXXX";
	ssize_t n, i, tot = 0, off, cur = 0;
	char buf[65535];
	int tmpfd;

	if (fd < 0 || com->y > endl || com->x > endl || com->x > com->y ||
	    com->x <= 0 || com->y <= 0)
		return 0;

	savefile();
	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf)))) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] != '\n')
				continue;
			++cur;
			if ((cur < com->x || cur > com->y)) {
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
	curl = com->x;
	if (curl > endl)
		curl = endl;
	change = 1;
	return 1;
}

static bool
writefile(edcom *com)
{
	ssize_t n, i, k, tot = 0, off, cur = 0;
	char buf[65535];
	int tmpfd;

	if (fd < 0)
		return 0;
	if (endl > 0 &&
	    (com->y > endl || com->x > endl || com->x > com->y || com->x <= 0 ||
		com->y <= 0))
		return 0;
	if ((tmpfd = open(lastfile, O_WRONLY | O_CREAT | O_TRUNC, 0644)) < 0)
		return 0;
	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf)))) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] != '\n')
				continue;
			++cur;
			if (cur >= com->x) {
				if ((k = write(tmpfd, buf + off, i - off + 1)) <
				    0) {
					close(tmpfd);
					return 0;
				}
				tot += k;
			}
			if (cur == com->y)
				goto ret;
			off = i + 1;
		}
	}
ret:
	printf("Write: %zu [%zu lines]\n", tot,
	    (endl > 0) ? cur - com->x + 1 : 0);
	close(tmpfd);
	change = 0;
	return 1;
}

static bool
join(edcom *com)
{
	char ntempl[] = "/tmp/aedjoinXXXXXX";
	ssize_t n, i, tot = 0, off, cur = 0;
	char buf[65535];
	bool flag = 0;
	int tmpfd;

	if (fd < 0 || com->y > endl || com->x > endl || com->x > com->y ||
	    com->x <= 0 || com->y <= 0)
		return 0;

	savefile();
	if ((tmpfd = mkstemp(ntempl)) < 0)
		return 0;
	lseek(fd, 0, SEEK_SET);
	while ((n = read(fd, buf, sizeof(buf)))) {
		for (i = off = 0; i < n; i++) {
			if (buf[i] != '\n')
				continue;
			++cur;
			if ((flag = (cur < com->x || cur + 1 > com->y)))
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
	curl = com->x;
	change = 1;
	return 1;
}

static void
setdefault(edcom *com)
{
	if (com->x != -1 && com->y != -1)
		return;
	switch (com->c) {
	case 'p':
	case 'n':
	case 'l':
	case 'd':
	case 'k':
	case 'm':
	case 't':
		com->x = com->y = curl;
		break;
	case 'r':
	case '=':
		com->x = com->y = endl;
		break;
	case 'j':
		com->x = curl;
		com->y = curl + 1;
	case 'w':
		com->x = 1;
		com->y = endl;
		break;
	}
}

static bool
exec(edcom *com)
{
	switch (com->c) {
	case 'q':
		if (change)
			return (change = 0);
		quit(0);
	case 'Q':
		change = 0;
		quit(0);
	case '\'':
		if (!isalpha((uint8_t)*com->arg))
			return 0;
		com->x = com->y = marks[tolower(*com->arg) - 'a'];
		return print(com, 0, 0);
	case 'p':
		return print(com, 0, 0);
	case 'j':
		return join(com);
	case 'n':
		return print(com, 1, 0);
	case 'w':
		return writefile(com);
	case 'd':
		return delete (com);
	case '=':
		if (com->x > endl || com->x <= 0)
			return 0;
		printf("%zu\n", com->x);
		return 1;
	case 'k':
		if (!isalpha((uint8_t)*com->arg))
			return 0;
		marks[tolower(*com->arg) - 'a'] = com->x;
		return 1;
	case 'f':
		puts(lastfile);
		return 1;
	case 'l':
		return print(com, 0, 1);
	case 'e':
		return edit(com);
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
	if (--c) {
		snprintf(lastfile, sizeof(lastfile), "%s", av[1]);
		if (!edit(NULL))
			goto err;
	}
	for (;;) {
		char buf[65535] = { 0 }, *s = NULL;
		edcom com = { .x = -1, .y = -1, .c = 'p' };

		if (!(fgets(buf, sizeof(buf) - 1, stdin)))
			goto err;
		buf[strcspn(buf, "\n")] = 0;
		if (!strlen(buf)) /* null command */
			com.y = com.x = curl + 1;
		else if (!(parse(buf, curl, endl, &com)))
			goto err;
		setdefault(&com);
		if (!(exec(&com)))
			goto err;

		continue;
	err:
		puts("?");
	}

	return 0;
}
