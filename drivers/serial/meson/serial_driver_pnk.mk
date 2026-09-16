#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson UART driver.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/meson/serial_driver_pnk.o serial/meson/serial_driver.o serial/meson/serial_driver_init_pnk.o util/pancake_ffi.o libsddf_util_debug.a util/pancake_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/meson/serial_driver_pnk.o: serial/meson/serial_driver_pnk.S |serial/meson
	$(CC) -c $(CFLAGS) -o $@ $<

serial/meson/serial_driver_pnk.S: serial/meson/serial_driver_pnk.pnk |serial/meson
	$(PANCAKE_COMPILER) $(PANCAKE_FLAGS) < $< > $@

serial/meson/serial_driver_pnk.pnk: $(DRIVER_PNK) |serial/meson
	cat $^ | cpp -P > $@

serial/meson/serial_driver_pre.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/meson $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/meson/serial_driver.o: serial/meson/serial_driver_pre.o
	$(OBJCOPY) --redefine-sym init=c_init --redefine-sym notified=c_notified $< $@

serial/meson/serial_driver_init_pnk.o: ${SERIAL_DRIVER_DIR}/uart_init_pnk.c |serial/meson $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/meson:
	mkdir -p $@

-include serial/meson/serial_driver.d

clean::
	rm -f serial/meson/serial_driver.[do] serial/meson/serial_driver_pnk.[oS]

clobber::
	rm -rf serial
