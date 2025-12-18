#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
#    the Synopsis DesignWare ABP UART driver

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
# Architecture-specific settings
ARCH := ${shell grep 'CONFIG_SEL4_ARCH  ' $(BOARD_DIR)/include/kernel/gen_config.h | cut -d' ' -f4}
$(info [ns16550a] Detected ARCH: $(ARCH) from $(BOARD_DIR))

# Detect compiler type
CC_IS_CLANG := $(shell $(CC) --version 2>/dev/null | grep -q clang && echo 1 || echo 0)

ifeq ($(ARCH),aarch64)
    PANCAKE_TARGET := arm8
    ifeq ($(CC_IS_CLANG),1)
        ASM_FLAGS := -target aarch64-none-elf $(if $(CPU),-mcpu=$(CPU))
    else
        ASM_FLAGS := $(if $(CPU),-mcpu=$(CPU))
    endif
else ifeq ($(ARCH),riscv64)
    PANCAKE_TARGET := riscv
    ifeq ($(CC_IS_CLANG),1)
        ASM_FLAGS := -target riscv64-none-elf -march=rv64imafdc
    else
        ASM_FLAGS := -march=rv64imafdc -mabi=lp64d
    endif
else
    $(warning [ns16550a] Unknown ARCH '$(ARCH)', defaulting to arm8)
    PANCAKE_TARGET := arm8
endif

$(info [ns16550a] Using PANCAKE_TARGET: $(PANCAKE_TARGET))

serial_driver.elf: serial_pnk.o serial/ns16550a/serial_driver.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

DRIVER_PNK = ${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_pnk.o: serial_pnk.S
	$(CC) -c $(ASM_FLAGS) $< -o $@

serial_pnk.S: $(DRIVER_PNK)
	cat $(DRIVER_PNK) | cpp -P | $(CAKE_COMPILER) --target=$(PANCAKE_TARGET) --pancake --main_return=true > $@

serial/ns16550a/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/ns16550a
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL -I${SERIAL_DRIVER_DIR}/include -o $@ $<
else
serial_driver.elf: serial/ns16550a/serial_driver.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

serial/ns16550a/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/ns16550a
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<
endif

serial/ns16550a:
	mkdir -p $@

-include serial/ns16550a/serial_driver.d

clean::
	rm -f serial/ns16550a/serial_driver.[do]
clobber:: clean
	rm -rf serial_driver.elf serial
