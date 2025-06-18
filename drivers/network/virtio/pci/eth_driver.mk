#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the VirtIO network PCI driver
#
# NOTES:
#   Generates eth_driver.elf
#   Assumes libsddf_util_debug.a is in LIBS

ETHERNET_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
ETHERNET_COMMON_DIR := $(dir $(lastword $(MAKEFILE_LIST)))/../common
# @billn this is not really elegant, should be going from sddf root
VIRTIO_TRANSPORT_DIR := $(dir $(lastword $(MAKEFILE_LIST)))/../../../../virtio/transport/

CHECK_NETDRV_FLAGS_MD5:=.netdrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

eth_driver.elf: network/virtio/pci/ethernet.o network/virtio/pci/transport.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

network/virtio/pci/ethernet.o: ${ETHERNET_COMMON_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS}
	mkdir -p network/virtio/pci
	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER_DIR} -o $@ $<

network/virtio/pci/transport.o: ${VIRTIO_TRANSPORT_DIR}/pci.c ${CHECK_NETDRV_FLAGS}
	mkdir -p network/virtio/pci
	${CC} -c ${CFLAGS} -o $@ $<

-include virtio/pci/ethernet.d
