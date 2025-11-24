#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build the virtIO block driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

VIRTIO_BLK_DRIVER_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))/../
VIRTIO_TRANSPORT_DIR := $(SDDF)/virtio/transport/

CHECK_BLKDRV_FLAGS_MD5:=.blkdrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_block} | shasum | sed 's/ *-//')

${CHECK_BLKDRV_FLAGS_MD5}:
	-rm -f .blkdrv_cflags-*
	touch $@

blk_driver.elf: blk/virtio/blk_driver.o blk/virtio/mmio/transport.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

blk/virtio/blk_driver.o: ${VIRTIO_BLK_DRIVER_DIR}/block.c ${CHECK_BLKDRV_FLAGS_MD5} $(SDDF_LIBC_INCLUDE)
	mkdir -p blk/virtio/mmio
	$(CC) -c $(CFLAGS) -I${VIRTIO_BLK_DRIVER_DIR}/include -o $@ $<

blk/virtio/mmio/transport.o: ${VIRTIO_TRANSPORT_DIR}/mmio.c ${CHECK_BLKDRV_FLAGS_MD5}
	mkdir -p blk/virtio/mmio
	${CC} -c ${CFLAGS} -o $@ $<

-include blk_driver.d

clean::
	rm -f blk/virtio/blk_driver.[do]

clobber::
	rm -rf blk
