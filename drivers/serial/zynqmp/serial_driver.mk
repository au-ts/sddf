#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the zynqmp UART driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

serial_driver.elf: serial/zynqmp/uart.o serial/zynqmp/uart_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/zynqmp/uart.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/zynqmp $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/zynqmp/uart_common.o: ${SERIAL_DRIVER_DIR}/uart_common.c |serial/zynqmp $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

-include serial_driver.d

serial/zynqmp:
	mkdir -p $@

clean::
	rm -f serial/zynqmp/serial_driver.[do] serial/zynqmp/serial_driver_pnk.[oS]

clobber::
	rm -rf serial
