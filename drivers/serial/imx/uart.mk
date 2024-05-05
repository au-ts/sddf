#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 UART driver

UART_DRIVER:= ${SDDF}/drivers/serial/imx

uart_driver.elf: serial/imx/uart_driver.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/imx/uart_driver.o: ${SDDF}/drivers/serial/imx/uart.c |serial/imx
	$(CC) -c $(CFLAGS) -I${UART_DRIVER}/include -o $@ $< 

-include uart_driver.d

serial/imx:
	mkdir -p serial/imx

clean::
	rm -f serial/imx/uart_driver.[do]

clobber::
	rm -rf serial
