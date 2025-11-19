#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# NOTES:
#  Generates timer_common.o

TIMER_COMMON_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

timer/timer_common.o: CFLAGS += -I${TIMER_COMMON_DIR}
timer/timer_common.o: ${TIMER_COMMON_DIR}/timer_common.c |timer $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

timer:
	mkdir -p timer

clean::
	rm -rf timer
