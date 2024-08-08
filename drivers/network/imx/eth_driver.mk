#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 NIC driver
#
# NOTES
#  Generates eth_driver.elf
#  Expects System Description File to set eth_regs to the address of
#  the registers
#  Expects libsddf_util_debug.a to be in LIBS

ETHERNET_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
CHECK_NETDRV_FLAGS_MD5:=.netdrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

eth_driver.elf: imx/ethernet.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

imx/ethernet.o: ${ETHERNET_DRIVER_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS_MD5}
	mkdir -p imx
	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER_DIR} -o $@ $<


-include imx/ethernet.d
