#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the VirtIO network driver
#
# NOTES:
#   Generates eth_driver.elf
#   Assumes libsddf_util_debug.a is in LIBS

ETHERNET_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
ETHERNET_COMMON_DIR := $(dir $(lastword $(MAKEFILE_LIST)))/../common
VIRTIO_TRANSPORT_DIR := $(SDDF)/virtio/transport/

CHECK_NETDRV_FLAGS_MD5:=.netdrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

eth_driver.elf: network/virtio/mmio/ethernet.o network/virtio/mmio/transport.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

network/virtio/mmio/ethernet.o: ${ETHERNET_COMMON_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS}
	mkdir -p network/virtio/mmio
	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER_DIR} -o $@ $<

network/virtio/mmio/transport.o: ${VIRTIO_TRANSPORT_DIR}/mmio.c ${CHECK_NETDRV_FLAGS}
	mkdir -p network/virtio/mmio
	${CC} -c ${CFLAGS} -o $@ $<

-include virtio/mmio/ethernet.d
