#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 NIC driver

ETHERNET_DRIVER:=${SDDF}/drivers/network/meson

ifeq ($(strip $(ETHERNET_CONFIG_INCLUDE)),)
$(error ETHERNET_CONFIG_INCLUDE must be specified)
endif


eth.elf: meson/ethernet.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

meson/ethernet.o: ${ETHERNET_DRIVER}/ethernet.c
	mkdir -p meson
	${CC} -c ${CFLAGS} -I ${ETHERNET_DRIVER} -MF meson/ethernet.d -o $@ $^

-include meson/ethernet.d
