#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
#    the PL011 UART driver
# Requires uart_base to be set to the mapped address of the UART
#    registers in the system description file

UART_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

uart_driver.elf: serial/arm/uart_driver.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

serial/arm/uart_driver.o: ${UART_DRIVER_DIR}/uart.c |serial/arm
	$(CC) -c $(CFLAGS) -I${UART_DRIVER_DIR}/include -o $@ $< 

serial/arm:
	mkdir -p $@

-include serial/arm/uart_driver.d

clean::
	rm -f serial/arm/uart_driver.[do]
clobber:: clean
	rm -rf uart_driver.elf serial

