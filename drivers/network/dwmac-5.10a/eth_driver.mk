#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Synopsys dwmac 5.10a NIC driver
#
# NOTES:
#   Generates eth_driver.elf (alternative unique name eth_driver_dwmac-5.10a.elf)
#   Assumes libsddf_util_debug.a is in LIBS

ETHERNET_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

CHECK_NETDRV_FLAGS_MD5:=.netdrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

eth_driver.elf eth_driver_dwmac-5.10a.elf: network/dwmac-5.10a/ethernet.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

network/dwmac-5.10a/ethernet.o: ${ETHERNET_DRIVER_DIR}ethernet.c ${CHECK_NETDRV_FLAGS}
	mkdir -p network/dwmac-5.10a
	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER_DIR} -o $@ $<

-include dwmac-5.10a/ethernet.d
