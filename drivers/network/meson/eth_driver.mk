#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Amlogic NIC driver
#
# NOTES:
#   Generates eth_driver.elf
#   Needs eth_regs to be set in System Description File
#   Assumes libsddf_util_debug.a is in LIBS

ETHERNET_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

CHECK_NETDRV_FLAGS_MD5:=.netdrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

eth_driver.elf: meson/ethernet.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

meson/ethernet.o: ${ETHERNET_DRIVER_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS_MD5}
	mkdir -p meson
	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER_DIR} -o $@ $<

-include meson/ethernet.d
