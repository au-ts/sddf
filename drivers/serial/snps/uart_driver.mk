#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
#    the Synopsis DesignWare ABP UART driver
# Requires uart_base to be set to the mapped address of the UART
#    registers in the system description file

UART_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

uart_driver.elf: serial/snps/uart_driver.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

serial/snps/uart_driver.o: ${UART_DRIVER_DIR}/uart.c |serial/snps
	$(CC) -c $(CFLAGS) -I${UART_DRIVER_DIR}/include -o $@ $<

serial/snps:
	mkdir -p $@

-include serial/snps/uart_driver.d

clean::
	rm -f serial/snps/uart_driver.[do]
clobber:: clean
	rm -rf uart_driver.elf serial