#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the JH7110 timer driver with Pancake support
#
# NOTES:
#  Generates timer_driver.elf
#  Expects libsddf_util_debug.a in ${LIBS}
#  Requires CAKE_COMPILER to be set for Pancake compilation

TIMER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

# Detect compiler type for consistent flag usage
CC_IS_CLANG := $(shell $(CC) --version 2>/dev/null | grep -q clang && echo 1 || echo 0)

# Set up architecture-specific assembly flags
ifeq ($(ARCH),riscv64)
    ifeq ($(CC_IS_CLANG),1)
        ASM_FLAGS := -target riscv64-none-elf -march=rv64imafdc
    else
        ASM_FLAGS := -march=rv64imafdc -mabi=lp64d
    endif
else
    ifeq ($(CC_IS_CLANG),1)
        ASM_FLAGS := -target aarch64-none-elf $(if $(CPU),-mcpu=$(CPU))
    else
        ASM_FLAGS := $(if $(CPU),-mcpu=$(CPU))
    endif
endif

ifeq ($(PANCAKE_TIMER),1)
# Pancake source files
TIMER_PNK = ${UTIL}/util.pnk \
	${TIMER_DIR}/timer.pnk

timer_driver.elf: timer/timer_pnk.o timer/timer.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

timer/timer.o: ${TIMER_DIR}/timer.c ${CHECK_FLAGS_BOARD_MD5} |timer
	${CC} ${CFLAGS} -DPANCAKE_TIMER -o $@ -c $<

timer/timer_pnk.o: timer/timer_pnk.S
	$(CC) $(ASM_FLAGS) -c $< -o $@

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
