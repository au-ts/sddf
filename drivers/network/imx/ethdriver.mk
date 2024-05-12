#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 NIC driver
#
# NOTES
#  Generates eth.elf
#  Expects System Description File to set eth_regs to the address of
#  the registers
#  Expects libsddf_util_debug.a to be in LIBS

ETHERNET_DRIVER:=${SDDF}/drivers/network/imx
CHECK_NETDRV_FLAGS_MD5:=.netdrv_cflags-$(shell echo -- ${CFLAGS} | shasum | sed 's/ *-//')

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

eth.elf: imx/ethernet.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

imx/ethernet.o: ${ETHERNET_DRIVER}/ethernet.c ${CHECK_NETDRV_FLAGS_MD5}
	mkdir -p imx
	${CC} -c ${CFLAGS} -I ${ETHERNET_DRIVER} -o $@ $<


-include imx/ethernet.d