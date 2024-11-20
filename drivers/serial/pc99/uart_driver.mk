#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the pc99 UART driver.
#
# NOTES:
#   Builds uart_driver.elf
#   Needs uart_base to be set to the mapped address of the UART
#    registers in the system description file

UART_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

uart_driver.elf: serial/pc99/uart_driver.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/pc99/uart_driver.o: ${UART_DRIVER_DIR}/uart.c |serial/pc99
	$(CC) -c $(CFLAGS) -I${UART_DRIVER_DIR}/include -o $@ $< 

serial/pc99:
	mkdir -p $@

-include serial/pc99/uart_driver.d

clean::
	rm -f serial/pc99/uart_driver.[do]

clobber::
	rm -rf serial
