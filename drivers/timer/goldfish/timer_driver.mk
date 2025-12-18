#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the goldfish-rtc timer driver with Pancake support
#
# NOTES:
#  Generates timer_driver.elf
#  Expects libsddf_util_debug.a to be in ${LIBS}
#  Requires CAKE_COMPILER to be set for Pancake compilation

TIMER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

ifeq ($(CC),clang)
    ifeq ($(ARCH),riscv64)
        CLANG_TARGET_FLAGS := -target riscv64-none-elf
    else
        CLANG_TARGET_FLAGS := -target aarch64-none-elf
    endif
else
    CLANG_TARGET_FLAGS :=
endif

ifeq ($(PANCAKE_DRIVER),1)
TIMER_PNK = ${UTIL}/util.pnk \
	${TIMER_DIR}/timer.pnk

timer_driver.elf: timer/timer_pnk.o timer/timer.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

timer/timer.o: ${TIMER_DIR}/timer.c ${CHECK_FLAGS_BOARD_MD5} |timer
	${CC} ${CFLAGS} -DPANCAKE_DRIVER -o $@ -c $<

ifeq ($(ARCH),riscv64)
timer/timer_pnk.o: timer/timer_pnk.S
	$(CC) $(CLANG_TARGET_FLAGS) -march=rv64imafdc -c $< -o $@
else
timer/timer_pnk.o: timer/timer_pnk.S
	$(CC) $(CLANG_TARGET_FLAGS) -c -mcpu=$(CPU) $< -o $@
endif

ifeq ($(ARCH),riscv64)
timer/timer_pnk.S: $(TIMER_PNK) | timer
	cat $(TIMER_PNK) | cpp -P | $(CAKE_COMPILER) --target=riscv --pancake --main_return=true > $@
else
timer/timer_pnk.S: $(TIMER_PNK) | timer
	cat $(TIMER_PNK) | cpp -P | $(CAKE_COMPILER) --target=arm8 --pancake --main_return=true > $@
endif
else
timer_driver.elf: timer/timer.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

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
