#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 UART driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
SERIAL_QUEUE_INCLUDE := ${SDDF}/include/sddf/serial

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
DRIVER_PNK = ${UTIL}/util.pnk \
	${SERIAL_QUEUE_INCLUDE}/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

CC_IS_CLANG := $(shell $(CC) --version 2>/dev/null | grep -q clang && echo yes || echo no)

ifeq ($(CC_IS_CLANG),yes)
    TARGET_FLAG := -target aarch64-none-elf
else
    TARGET_FLAG :=
endif

serial_pnk.o: serial_pnk.S
	$(CC) -c -mcpu=$(CPU) $(TARGET_FLAG) $< -o $@

serial_pnk.S: $(DRIVER_PNK)
	cat $(DRIVER_PNK) | cpp -P | $(CAKE_COMPILER) --target=arm8 --pancake --main_return=true > $@

serial_driver.elf: serial_pnk.o serial/imx/serial_driver.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/imx/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/imx
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<
else
serial_driver.elf: serial/imx/serial_driver.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/imx/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/imx
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<
endif

-include serial_driver.d

serial/imx:
	mkdir -p $@

clean::
	rm -f serial/imx/serial_driver.[do]

clobber::
	rm -rf serial
