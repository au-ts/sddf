#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the virtio console driver.

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
VIRTIO_TRANSPORT_DIR := $(SDDF)/virtio/transport/

serial_driver.elf: serial/virtio/serial_driver.o serial/virtio/mmio_transport.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/virtio/serial_driver.o: ${SERIAL_DRIVER_DIR}/console.c |serial/virtio
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<

serial/virtio/mmio_transport.o: ${VIRTIO_TRANSPORT_DIR}/mmio.c
	${CC} -c ${CFLAGS} -DVIRTIO_MMIO_TRANSPORT_FOR_CONSOLE -o $@ $<

serial/virtio:
	mkdir -p $@

-include serial/virtio/serial_driver.d

clean::
	rm -f serial/virtio/serial_driver.[do]

clobber::
	rm -rf serial
