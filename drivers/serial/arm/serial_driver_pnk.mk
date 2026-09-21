#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the PL011 UART driver

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

DRIVER_PNK = \
	${UTIL}/util.pnk \
	${SDDF}/include/sddf/serial/queue.pnk \
	${SERIAL_DRIVER_DIR}/uart.pnk

serial_driver.elf: serial/arm/serial_driver_pnk.o serial/arm/serial_driver.o serial/arm/serial_driver_init_pnk.o util/pancake_ffi.o util/pancake_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/arm/serial_driver_pnk.o: serial/arm/serial_driver_pnk.S |serial/arm
	$(CC) -c $(CFLAGS) -o $@ $<

serial/arm/serial_driver_pnk.S: serial/arm/serial_driver_pnk.pnk |serial/arm
	$(PANCAKE_COMPILER) $(PANCAKE_FLAGS) < $< > $@

serial/arm/serial_driver_pnk.pnk: $(DRIVER_PNK) |serial/arm
	cat $^ | $(CPP) -P -CC -nostdinc > $@

serial/arm/serial_driver_pre.o: ${SERIAL_DRIVER_DIR}/uart.c |serial/arm $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/arm/serial_driver.o: serial/arm/serial_driver_pre.o
	$(OBJCOPY) --redefine-sym init=c_init --redefine-sym notified=c_notified $< $@

serial/arm/serial_driver_init_pnk.o: ${SERIAL_DRIVER_DIR}/uart_init_pnk.c |serial/arm $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/arm:
	mkdir -p $@

-include serial/arm/serial_driver.d

clean::
	rm -f serial/arm/serial_driver_init_pnk.[do] serial/arm/serial_driver.o
	rm -f serial/arm/serial_driver_pre.[do] serial/arm/serial_driver_pnk.pnk
	rm -f serial/arm/serial_driver_pnk.[doS]

clobber:: clean
	rm -rf serial_driver.elf serial
