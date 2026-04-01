#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the GENET NIC driver
#
# NOTES
#  Generates eth_driver.elf (alternative unique name eth_driver_genet.elf)
#  Expects libsddf_util_debug.a to be in LIBS

ETHERNET_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
CHECK_NETDRV_GENET_FLAGS_MD5:=.netdrv_genet_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETDRV_GENET_FLAGS_MD5}:
	-rm -f .netdrv_genet_cflags-*
	touch $@

eth_driver_genet.elf: network/genet/ethernet.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

network/genet/ethernet.o: ${ETHERNET_DRIVER_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS_MD5} | $(SDDF_LIBC_INCLUDE)
	mkdir -p network/genet
	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER_DIR} -o $@ $<

-include genet/ethernet.d
