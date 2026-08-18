#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 UART driver.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
serial_driver.elf: serial/imx/serial_pnk.o serial/imx/serial_driver.o util/pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/imx/serial_pnk.o: serial/imx/serial_pnk.S |serial/imx
	$(CC) -c $(CFLAGS) -o $@ $<

serial/imx/serial_pnk.S: $(DRIVER_PNK) |serial/imx
	cat $(DRIVER_PNK) | cpp -P | $(PANCAKE_COMPILER) $(PANCAKE_FLAGS) > $@

serial/imx/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/imx $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<
else
serial_driver.elf: serial/imx/serial_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/imx/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/imx $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<
endif

-include serial_driver.d

serial/imx:
	mkdir -p $@

clean::
	rm -f serial/imx/serial_driver.[do] serial/imx/serial_pnk.[oS]

clobber::
	rm -rf serial
