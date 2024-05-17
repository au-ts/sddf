#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 UART driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.
# Requires uart_regs to be set to the mapped base of the UART registers
# in the system description file.

UART_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

uart_driver.elf: serial/imx/uart_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/imx/uart_driver.o: ${UART_DRIVER_DIR}/uart.c |serial/imx
	$(CC) -c $(CFLAGS) -I${UART_DRIVER_DIR}/include -o $@ $< 

-include uart_driver.d

serial/imx:
	mkdir -p $@

clean::
	rm -f serial/imx/uart_driver.[do]

clobber::
	rm -rf serial
