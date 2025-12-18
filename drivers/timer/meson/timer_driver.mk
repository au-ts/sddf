#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson timer driver with Pancake support
#
# NOTES:
#  Generates timer_driver.elf
#  Expects libsddf_util_debug.a in ${LIBS}
#  Requires CAKE_COMPILER to be set for Pancake compilation

TIMER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

ifeq ($(PANCAKE_TIMER),1)
# Set up clang target flags if using clang
ifeq ($(CC),clang)
    CLANG_TARGET_FLAGS := -target aarch64-none-elf
else
    CLANG_TARGET_FLAGS :=
endif

# Pancake source files
TIMER_PNK = ${UTIL}/util.pnk \
	${TIMER_DIR}/timer.pnk

timer_driver.elf: timer/timer_pnk.o timer/timer.o pancake_ffi.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

timer/timer.o: ${TIMER_DIR}/timer.c ${CHECK_FLAGS_BOARD_MD5} |timer
	${CC} ${CFLAGS} -DPANCAKE_TIMER -o $@ -c $<

timer/timer_pnk.o: timer/timer_pnk.S
	$(CC) $(CLANG_TARGET_FLAGS) -c -mcpu=$(CPU) $< -o $@

timer/timer_pnk.S: $(TIMER_PNK) | timer
	cat $(TIMER_PNK) | cpp -P | $(CAKE_COMPILER) --target=arm8 --pancake --main_return=true > $@
else
timer_driver.elf: timer/timer.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

timer/timer.o: ${TIMER_DIR}/timer.c ${CHECK_FLAGS_BOARD_MD5} |timer
	${CC} ${CFLAGS} -o $@ -c $<
endif

timer:
	mkdir -p timer

clean::
	rm -rf timer
	rm -f timer/timer_pnk.[So]

clobber::
	rm -f timer_driver.elf
