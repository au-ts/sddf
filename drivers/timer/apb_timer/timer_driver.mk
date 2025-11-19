#
# Copyright 2025, UNSW
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

#timer_driver.elf: timer/timer.o
#	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

#timer/timer.o: ${TIMER_DIR}/timer.c  ${CHECK_FLAGS_BOARD_MD5} $(SDDF_LIBC_INCLUDE)|timer
#	${CC} ${CFLAGS} -o $@ -c $<


timer_driver.elf: timer/timer_driver.o timer/timer_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

timer/timer_driver.o: CFLAGS+=-I${TIMER_DIR}
timer/timer_driver.o: ${TIMER_DIR}/timer.c ${CHECK_FLAGS_BOARD_MD5} $(SDDF_LIBC_INCLUDE)|timer
	${CC} ${CFLAGS} -c -o $@ $<

timer/timer_common.o: CFLAGS+=-I${TIMER_DIR}
timer/timer_common.o: ${TIMER_DIR}/../timer_common.c |timer $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<


timer:
	mkdir -p timer

clean::
	rm -rf timer
clobber::
	rm -f timer_driver.elf
