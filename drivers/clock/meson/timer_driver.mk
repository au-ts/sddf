#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson timer driver
#
# NOTES:
#  Generates timer_driver.elf
#  Expects system file to set variable 'gpt_regs' to the address of
#     the timer registers (physical address 0xffd0f000 on a meson-g12 SoC)
#  Expects libsddf_util_debug.a in ${LIBS}

TIMER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

timer_driver.elf: timer/timer.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

timer/timer.o: ${TIMER_DIR}/timer.c  ${CHECK_FLAGS_BOARD_MD5} |timer
	${CC} ${CFLAGS} -o $@ -c $<

timer:
	mkdir -p timer

clean::
	rm -rf timer
clobber::
	rm -f timer_driver.elf
