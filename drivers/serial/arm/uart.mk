#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the PL011 UART driver

UART_DRIVER:= ${SDDF}/drivers/serial/arm

uart_driver.elf: serial/arm/uart_driver.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/arm/uart_driver.o: ${SDDF}/drivers/serial/arm/uart.c |serial/arm
	$(CC) -c $(CFLAGS) -I${UART_DRIVER}/include -o $@ $< 

serial/arm:
	mkdir -p $@
-include serial/arm/uart_driver.d

clean::
	rm -f serial/arm/uart_driver.[do]
clobber:: clean
	rm -rf uart_driver.elf serial

