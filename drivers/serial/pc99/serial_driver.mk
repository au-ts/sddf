#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the PC99 UART driver.
#
# NOTES:
#   Builds serial_driver.elf

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

serial_driver.elf: serial/pc99/uart.o serial/pc99/uart_common.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/pc99/uart.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/pc99 $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/pc99/uart_common.o: ${SERIAL_DRIVER_DIR}/uart_common.c |serial/pc99 $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/pc99:
	mkdir -p $@

-include serial/pc99/serial_driver.d

clean::
	rm -f serial/pc99/uart.[do] serial/pc99/uart_common.[do]

clobber::
	rm -rf serial