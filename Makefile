CC = cc
CFLAGS = -Wall -O2
TARGET = aed
PREFIX ?= /usr/local
BINDIR = $(DESTDIR)$(PREFIX)/bin

all: $(TARGET)

$(TARGET): aed.c
	$(CC) $(CFLAGS) -o $(TARGET) aed.c

install: $(TARGET)
	mkdir -p $(BINDIR)
	install -m 755 $(TARGET) $(BINDIR)/$(TARGET)

uninstall:
	rm -f $(BINDIR)/$(TARGET)

clean:
	rm -f $(TARGET)

.PHONY: all install uninstall clean
