#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 UART driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

serial_driver.elf: serial/imx/serial_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/imx/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/imx
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

-include serial_driver.d

serial/imx:
	mkdir -p $@

clean::
	rm -f serial/imx/serial_driver.[do]

clobber::
	rm -rf serial
