#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Synopsis DesignWare ABP UART driver

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/ns16550a/serial_driver_pnk.o serial/ns16550a/serial_driver.o util/pancake_ffi.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/ns16550a/serial_driver_pnk.o: serial/ns16550a/serial_driver_pnk.S |serial/ns16550a
	$(CC) -c $(CFLAGS) -o $@ $<

serial/ns16550a/serial_driver_pnk.S: $(DRIVER_PNK) |serial/ns16550a
	cat $(DRIVER_PNK) | cpp -P > /workspaces/sddf/1.pnk
	cat $(DRIVER_PNK) | cpp -P | $(PANCAKE_COMPILER) $(PANCAKE_FLAGS) > $@

serial/ns16550a/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/ns16550a $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<
else
serial_driver.elf: serial/ns16550a/serial_driver.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

serial/ns16550a/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/ns16550a $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<
endif

serial/ns16550a:
	mkdir -p $@

-include serial/ns16550a/serial_driver.d

clean::
	rm -f serial/ns16550a/serial_driver.[do] serial/ns16550a/serial_driver_pnk.[oS]
clobber:: clean
	rm -rf serial_driver.elf serial
