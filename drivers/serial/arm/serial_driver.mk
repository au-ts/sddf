#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
#    the PL011 UART driver

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

serial_driver.elf: serial/arm/serial_driver.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

serial/arm/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/arm
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/arm:
	mkdir -p $@

-include serial/arm/serial_driver.d

clean::
	rm -f serial/arm/serial_driver.[do]
clobber:: clean
	rm -rf serial_driver.elf serial
