#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 NIC driver

ETHERNET_DRIVER:=${SDDF}/drivers/network/meson

CHECK_NETDRV_FLAGS_MD5:=.netdrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | md5sum | sed 's/  *-//')

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

eth.elf: meson/ethernet.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

meson/ethernet.o: ${ETHERNET_DRIVER}/ethernet.c ${CHECK_NETDRV_FLAGS}
	mkdir -p meson
	${CC} -c ${CFLAGS} -I ${ETHERNET_DRIVER} -MF meson/ethernet.d -o $@ $^

-include meson/ethernet.d
