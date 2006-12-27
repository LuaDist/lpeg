CWARNS = -Wall -W -pedantic \
        -Waggregate-return \
        -Wcast-align \
        -Wmissing-prototypes \
        -Wnested-externs \
        -Wpointer-arith \
        -Wshadow \
        -Wwrite-strings
#       -Wcast-qual
#       -Wtraditional

COPT = -O2 -DNDEBUG
CFLAGS = $(CWARNS) -ansi $(COPT) -I../lua
CC = gcc

lpeg.so: lpeg.c
	$(CC) $(CFLAGS) -shared -o lpeg.so lpeg.c

