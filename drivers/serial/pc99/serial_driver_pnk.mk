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

DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/pc99/serial_driver_pnk.o serial/pc99/uart_pnk_wrapper.o serial/pc99/uart_common.o util/pancake_ffi.o libsddf_util_debug.a util/pancake_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/pc99/serial_driver_pnk.o: serial/pc99/serial_driver_pnk.S |serial/pc99
	$(CC) -c $(CFLAGS) -o $@ $<

serial/pc99/serial_driver_pnk.S: serial/pc99/serial_driver_pnk.pnk |serial/pc99
	$(PANCAKE_COMPILER) $(PANCAKE_FLAGS) < $< > $@

serial/pc99/serial_driver_pnk.pnk: $(DRIVER_PNK) |serial/pc99
	cat $^ | cpp -P -nostdinc > $@

serial/pc99/uart_pnk_wrapper.o: ${SERIAL_DRIVER_DIR}/uart_pnk_wrapper.c |serial/pc99 $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/pc99/uart_common.o: ${SERIAL_DRIVER_DIR}/uart_common.c |serial/pc99 $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/pc99:
	mkdir -p $@

-include serial/pc99/serial_driver.d

clean::
	rm -f serial/pc99/serial_driver_pnk.[doS] serial/pc99/serial_driver_pnk.pnk
	rm -f serial/pc99/uart_pnk_wrapper.[do] serial/pc99/uart_common.[do]

clobber::
	rm -rf serial