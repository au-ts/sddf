#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson UART driver.
#
# NOTES:
#   Builds uart_driver.elf
#   Needs uart_base to be set to the mapped address of the UART
#    registers in the system description file

UART_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

uart_driver.elf: serial/meson/uart_driver.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/meson/uart_driver.o: ${UART_DRIVER_DIR}/uart.c |serial/meson
	$(CC) -c $(CFLAGS) -I${UART_DRIVER_DIR}/include -o $@ $< 

serial/meson:
	mkdir -p $@

-include serial/meson/uart_driver.d

clean::
	rm -f serial/meson/uart_driver.[do]

clobber::
	rm -rf serial
