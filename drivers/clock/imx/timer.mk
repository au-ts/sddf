#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 timer driver

TIMER_DIR=$(dir $(lastword $(MAKEFILE_LIST)))
TIMER_OBJS := timer/timer.o libsddf_util_debug.a
timer.elf: $(TIMER_OBJS)
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

timer/timer.o: ${TIMER_DIR}/timer.c ${CHECK_FLAGS_BOARD_MD5} |timer
	${CC} ${CFLAGS} -o $@ -c $<

timer:
	mkdir -p timer
