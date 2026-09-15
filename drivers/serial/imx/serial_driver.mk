#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 UART driver.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

serial_driver.elf: serial/imx/uart.o serial/imx/uart_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/imx/uart.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/imx $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/imx/uart_common.o: ${SERIAL_DRIVER_DIR}/uart_common.c |serial/imx $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

-include serial_driver.d

serial/imx:
	mkdir -p $@

clean::
	rm -f serial/imx/serial_driver.[do] serial/imx/serial_driver_pnk.[oS]

clobber::
	rm -rf serial
