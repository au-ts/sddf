#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the timer client library

TIMER_CLIENT := ${SDDF}/timer/client

timer/client/client.o: CFLAGS+=-MF timerclient.d
timer/client/client.o: ${TIMER_CLIENT}/client.c
	mkdir -p $(dir $@)
	${CC} ${CFLAGS} -c -o $@ $<

libtimerclient.a: timer/client/client.o
	ar cr $@ $^

-include timer/client/timerclient.d

clean::
	${RM} -rf timer
clobber:: clean
	${RM} -f libtimerclient.a
