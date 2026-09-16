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

serial_driver.elf: serial/ns16550a/serial_driver_pnk.o serial/ns16550a/serial_driver.o serial/ns16550a/serial_driver_init_pnk.o util/pancake_ffi.o libsddf_util_debug.a util/pancake_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/ns16550a/serial_driver_pnk.o: serial/ns16550a/serial_driver_pnk.S |serial/ns16550a
	$(CC) -c $(CFLAGS) -o $@ $<

serial/ns16550a/serial_driver_pnk.S: serial/ns16550a/serial_driver_pnk.pnk |serial/ns16550a
	$(PANCAKE_COMPILER) $(PANCAKE_FLAGS) < $< > $@

serial/ns16550a/serial_driver_pnk.pnk: $(DRIVER_PNK) |serial/ns16550a
	cat $^ | cpp -P -nostdinc > $@

serial/ns16550a/serial_driver_pre.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/ns16550a $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/ns16550a/serial_driver.o: serial/ns16550a/serial_driver_pre.o
	$(OBJCOPY) --redefine-sym init=c_init --redefine-sym notified=c_notified $< $@

serial/ns16550a/serial_driver_init_pnk.o: ${SERIAL_DRIVER_DIR}/uart_init_pnk.c |serial/ns16550a $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/ns16550a:
	mkdir -p $@

-include serial/ns16550a/serial_driver.d

clean::
	rm -f serial/ns16550a/serial_driver.[do] serial/ns16550a/serial_driver_pnk.[oS]
clobber:: clean
	rm -rf serial_driver.elf serial
