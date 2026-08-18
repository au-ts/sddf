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

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/pc99/serial_driver_pnk.o serial/pc99/serial_driver.o util/pancake_ffi.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/pc99/serial_driver_pnk.o: serial/pc99/serial_driver_pnk.S |serial/pc99
	$(CC) -c $(CFLAGS) -o $@ $<

serial/pc99/serial_driver_pnk.S: $(DRIVER_PNK) |serial/pc99
	cat $(DRIVER_PNK) | cpp -P | $(PANCAKE_COMPILER) $(PANCAKE_FLAGS) > $@

serial/pc99/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/pc99 $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<
else
serial_driver.elf: serial/pc99/serial_driver.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/pc99/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/pc99 $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<
endif

serial/pc99:
	mkdir -p $@

-include serial/pc99/serial_driver.d

clean::
	rm -f serial/pc99/serial_driver.[do] serial/pc99/serial_driver_pnk.[oS]

clobber::
	rm -rf serial