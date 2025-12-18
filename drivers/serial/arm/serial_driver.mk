#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
#    the PL011 UART driver

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

ifeq ($(PANCAKE_SERIAL_DRIVER),1)

CC_IS_CLANG := $(shell $(CC) --version 2>/dev/null | grep -q clang && echo 1 || echo 0)

ifeq ($(CC_IS_CLANG),1)
    TARGET_FLAG := -target aarch64-none-elf
else
    TARGET_FLAG :=
endif

serial_driver.elf: serial_pnk.o serial/arm/serial_driver.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

DRIVER_PNK = ${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_pnk.o: serial_pnk.S
	$(CC) -c -mcpu=$(CPU) $(TARGET_FLAG) $< -o $@

serial_pnk.S: $(DRIVER_PNK)
	cat $(DRIVER_PNK) | cpp -P | $(CAKE_COMPILER) --target=arm8 --pancake --main_return=true > $@

serial/arm/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/arm
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL -I${SERIAL_DRIVER_DIR}/include -o $@ $<
else
serial_driver.elf: serial/arm/serial_driver.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

serial/arm/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/arm
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<
endif

serial/arm:
	mkdir -p $@

-include serial/arm/serial_driver.d

clean::
	rm -f serial/arm/serial_driver.[do]
clobber:: clean
	rm -rf serial_driver.elf serial
