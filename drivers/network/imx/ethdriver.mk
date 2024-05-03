#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 NIC driver

ETHERNET_DRIVER:=${SDDF}/drivers/network/imx

eth.elf: imx/ethernet.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

imx/ethernet.o: ${ETHERNET_DRIVER}/ethernet.c
	mkdir -p imx
	${CC} -c ${CFLAGS} -I ${ETHERNET_DRIVER} -o $@ $^

-include imx/ethernet.d
