#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build the virtIO block driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.
# Expects the 'blk_regs' variable to be set by the Microkit SDF

VIRTIO_BLK_DRIVER_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

blk_driver.elf: blk/virtio/blk_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

blk/virtio/blk_driver.o: ${VIRTIO_BLK_DRIVER_DIR}/block.c |blk/virtio
	$(CC) -c $(CFLAGS) -I${VIRTIO_BLK_DRIVER_DIR}/include -o $@ $<

-include blk_driver.d

blk/virtio:
	mkdir -p $@

clean::
	rm -f blk/virtio/blk_driver.[do]

clobber::
	rm -rf blk
