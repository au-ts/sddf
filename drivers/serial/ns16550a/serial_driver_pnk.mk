#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Synopsis DesignWare ABP UART driver

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/ns16550a/serial_driver_pnk.o serial/ns16550a/uart_pnk_wrapper.o serial/ns16550a/uart_common.o util/pancake_ffi.o libsddf_util_debug.a util/pancake_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/ns16550a/serial_driver_pnk.o: serial/ns16550a/serial_driver_pnk.S |serial/ns16550a
	$(CC) -c $(CFLAGS) -o $@ $<

serial/ns16550a/serial_driver_pnk.S: serial/ns16550a/serial_driver_pnk.pnk |serial/ns16550a
	$(PANCAKE_COMPILER) $(PANCAKE_FLAGS) < $< > $@

serial/ns16550a/serial_driver_pnk.pnk: $(DRIVER_PNK) |serial/ns16550a
	cat $^ | cpp -P -nostdinc > $@

serial/ns16550a/uart_pnk_wrapper.o: ${SERIAL_DRIVER_DIR}/uart_pnk_wrapper.c |serial/ns16550a $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/ns16550a/uart_common.o: ${SERIAL_DRIVER_DIR}/uart_common.c |serial/ns16550a $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/ns16550a:
	mkdir -p $@

-include serial/ns16550a/serial_driver.d

clean::
	rm -f serial/ns16550a/serial_driver_pnk.[doS] serial/ns16550a/serial_driver_pnk.pnk
	rm -f serial/ns16550a/uart_pnk_wrapper.[do] serial/ns16550a/uart_common.[do]

clobber:: clean
	rm -rf serial_driver.elf serial
