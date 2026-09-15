#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 UART driver.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/imx/serial_driver_pnk.o serial/imx/uart_pnk_wrapper.o serial/imx/uart_common.o util/pancake_ffi.o util/pancake_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/imx/serial_driver_pnk.o: serial/imx/serial_driver_pnk.S |serial/imx
	$(CC) -c $(CFLAGS) -o $@ $<

serial/imx/serial_driver_pnk.S: serial/imx/serial_driver_pnk.pnk |serial/imx
	$(PANCAKE_COMPILER) $(PANCAKE_FLAGS) < $< > $@

serial/imx/serial_driver_pnk.pnk: $(DRIVER_PNK) |serial/imx
	cat $^ | cpp -P -nostdinc > $@

serial/imx/uart_pnk_wrapper.o: ${SERIAL_DRIVER_DIR}/uart_pnk_wrapper.c |serial/imx $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/imx/uart_common.o: ${SERIAL_DRIVER_DIR}/uart_common.c |serial/imx $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<

-include serial_driver.d

serial/imx:
	mkdir -p $@

clean::
	rm -f serial/imx/serial_driver_pnk.[doS] serial/imx/serial_driver_pnk.pnk
	rm -f serial/imx/uart_pnk_wrapper.[do] serial/imx/uart_common.[do]

clobber::
	rm -rf serial
