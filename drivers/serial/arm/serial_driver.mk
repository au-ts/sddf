#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the PL011 UART driver

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/arm/serial_driver_pnk.o serial/arm/serial_driver.o util/pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/arm/serial_driver_pnk.o: serial/arm/serial_driver_pnk.S |serial/arm
	$(CC) -c $(CFLAGS) -o $@ $<

serial/arm/serial_driver_pnk.S: $(DRIVER_PNK) |serial/arm
	cat $(DRIVER_PNK) | cpp -P | $(PANCAKE_COMPILER) $(PANCAKE_FLAGS) > $@

serial/arm/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/arm $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<
else
serial_driver.elf: serial/arm/serial_driver.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

serial/arm/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/arm $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<
endif

serial/arm:
	mkdir -p $@

-include serial/arm/serial_driver.d

clean::
	rm -f serial/arm/serial_driver.[do] serial/arm/serial_driver_pnk.[oS]
clobber:: clean
	rm -rf serial_driver.elf serial
