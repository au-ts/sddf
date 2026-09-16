#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the zynqmp UART driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/zynqmp/serial_driver_pnk.o serial/zynqmp/serial_driver.o serial/zynqmp/serial_driver_init_pnk.o util/pancake_ffi.o libsddf_util_debug.a util/pancake_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/zynqmp/serial_driver_pnk.o: serial/zynqmp/serial_driver_pnk.S |serial/zynqmp
	$(CC) -c $(CFLAGS) -o $@ $<

serial/zynqmp/serial_driver_pnk.S: serial/zynqmp/serial_driver_pnk.pnk |serial/zynqmp
	$(PANCAKE_COMPILER) $(PANCAKE_FLAGS) < $< > $@

serial/zynqmp/serial_driver_pnk.pnk: $(DRIVER_PNK) |serial/zynqmp
	cat $^ | cpp -P -nostdinc > $@

serial/zynqmp/serial_driver_pre.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/zynqmp $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/zynqmp/serial_driver.o: serial/zynqmp/serial_driver_pre.o
	$(OBJCOPY) --redefine-sym init=c_init --redefine-sym notified=c_notified $< $@

serial/zynqmp/serial_driver_init_pnk.o: ${SERIAL_DRIVER_DIR}/uart_init_pnk.c |serial/zynqmp $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

-include serial_driver.d

serial/zynqmp:
	mkdir -p $@

clean::
	rm -f serial/zynqmp/serial_driver.[do] serial/zynqmp/serial_driver_pnk.[oS]

clobber::
	rm -rf serial
