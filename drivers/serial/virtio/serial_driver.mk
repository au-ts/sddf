#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the virtio console driver.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
VIRTIO_TRANSPORT_DIR := $(SDDF)/virtio/transport/

serial/virtio/mmio/transport.o: ${VIRTIO_TRANSPORT_DIR}/mmio.c | $(SDDF_LIBC_INCLUDE)
	mkdir -p serial/virtio/mmio
	${CC} -c ${CFLAGS} -o $@ $<

serial_driver.elf: serial/virtio/serial_driver.o libsddf_util_debug.a serial/virtio/mmio/transport.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/virtio/serial_driver.o: ${SERIAL_DRIVER_DIR}/console.c |serial/virtio $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/virtio:
	mkdir -p $@

-include serial/virtio/serial_driver.d serial/virtio/mmio/transport.d

clean::
	rm -f serial/virtio/serial_driver.[do]

clobber::
	rm -rf serial
