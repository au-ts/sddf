#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the virtio console driver.
#
# NOTES:
#   Builds serial_driver.elf

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

serial_driver.elf: serial/virtio/serial_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/virtio/serial_driver.o: ${SERIAL_DRIVER_DIR}/console.c |serial/virtio
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/virtio:
	mkdir -p $@

-include serial/virtio/serial_driver.d

clean::
	rm -f serial/virtio/serial_driver.[do]

clobber::
	rm -rf serial
