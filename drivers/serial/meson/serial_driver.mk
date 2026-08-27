#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson UART driver.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/meson/serial_driver_pnk.o serial/meson/serial_driver.o util/pancake_ffi.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/meson/serial_driver_pnk.o: serial/meson/serial_driver_pnk.S |serial/meson
	$(CC) -c $(CFLAGS) -o $@ $<

serial/meson/serial_driver_pnk.S: $(DRIVER_PNK) |serial/meson
	cat $(DRIVER_PNK) | cpp -P | $(PANCAKE_COMPILER) $(PANCAKE_FLAGS) > $@

serial/meson/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/meson $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<
else
serial_driver.elf: serial/meson/serial_driver.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/meson/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/meson $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<
endif

serial/meson:
	mkdir -p $@

-include serial/meson/serial_driver.d

clean::
	rm -f serial/meson/serial_driver.[do] serial/meson/serial_driver_pnk.[oS]

clobber::
	rm -rf serial
