#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson UART driver.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

serial_driver.elf: serial/meson/serial_driver.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/meson/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/meson $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/meson:
	mkdir -p $@

-include serial/meson/serial_driver.d

clean::
	rm -f serial/meson/serial_driver.[do]

clobber::
	rm -rf serial
