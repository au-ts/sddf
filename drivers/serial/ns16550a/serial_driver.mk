#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Synopsis DesignWare ABP UART driver

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

serial_driver.elf: serial/ns16550a/uart.o serial/ns16550a/uart_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/ns16550a/uart.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/ns16550a $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/ns16550a/uart_common.o: ${SERIAL_DRIVER_DIR}/uart_common.c |serial/ns16550a $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/ns16550a:
	mkdir -p $@

-include serial/ns16550a/serial_driver.d

clean::
	rm -f serial/ns16550a/serial_driver.[do] serial/ns16550a/serial_driver_pnk.[oS]
clobber:: clean
	rm -rf serial_driver.elf serial
