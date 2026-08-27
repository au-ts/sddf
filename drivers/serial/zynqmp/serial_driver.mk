#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the zynqmp UART driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/zynqmp/serial_driver_pnk.o serial/zynqmp/serial_driver.o util/pancake_ffi.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/zynqmp/serial_driver_pnk.o: serial/zynqmp/serial_driver_pnk.S |serial/zynqmp
	$(CC) -c $(CFLAGS) -o $@ $<

serial/zynqmp/serial_driver_pnk.S: $(DRIVER_PNK) |serial/zynqmp
	cat $(DRIVER_PNK) | cpp -P | $(PANCAKE_COMPILER) $(PANCAKE_FLAGS) > $@

serial/zynqmp/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/zynqmp $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL_DRIVER -I${SERIAL_DRIVER_DIR}/include -o $@ $<
else
serial_driver.elf: serial/zynqmp/serial_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/zynqmp/serial_driver.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/zynqmp $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<
endif

-include serial_driver.d

serial/zynqmp:
	mkdir -p $@

clean::
	rm -f serial/zynqmp/serial_driver.[do] serial/zynqmp/serial_driver_pnk.[oS]

clobber::
	rm -rf serial
