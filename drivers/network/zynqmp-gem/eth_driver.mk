#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the zynqmp-gem NIC driver
#
# NOTES
#  Generates eth_driver_znyqmp_gem.elf.elf
#  Expects libsddf_util_debug.a to be in LIBS

ETHERNET_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
CHECK_NETDRV_FLAGS_MD5:=.netdrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

eth_driver_znyqmp_gem.elf: network/zynqmp-gem/ethernet.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

network/zynqmp-gem/ethernet.o: ${ETHERNET_DRIVER_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS_MD5}
	mkdir -p network/zynqmp-gem
	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER_DIR} -o $@ $<


-include zynqmp-gem/ethernet.d
