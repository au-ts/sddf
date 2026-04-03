#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the apb_timer driver
#
# NOTES:
#  Generates timer_driver.elf
#  Expects libsddf_util_debug.a in ${LIBS}

TIMER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

timer_driver.elf: timer/timer_driver.o timer/timer_common.o timer/time_conv.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

timer/timer_driver.o: CFLAGS+=-I${TIMER_DIR}
timer/timer_driver.o: ${TIMER_DIR}/timer.c ${CHECK_FLAGS_BOARD_MD5} $(SDDF_LIBC_INCLUDE)|timer
	${CC} ${CFLAGS} -c -o $@ $<

timer/timer_common.o: CFLAGS+=-I${TIMER_DIR}
timer/timer_common.o: ${TIMER_DIR}/../timer_common.c |timer $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

timer/time_conv.o: CFLAGS+=-I${TIMER_DIR}
timer/time_conv.o: ${TIMER_DIR}/../time_conv.c |timer $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

timer:
	mkdir -p timer

clean::
	rm -rf timer
clobber::
	rm -f timer_driver.elf

