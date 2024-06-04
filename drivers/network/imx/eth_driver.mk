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

ETHERNET_PNK = ${UTIL}/util.🥞 \
		${NETWORK_QUEUE_INCLUDE}/queue.🥞 \
		${ETHERNET_DRIVER_DIR}/device_helper.🥞 \
		${ETHERNET_DRIVER_DIR}/driver_heap.🥞 \
		${ETHERNET_DRIVER_DIR}/ethernet.🥞

ethernet_pnk.S: $(ETHERNET_PNK)
	cat $(ETHERNET_PNK) | cpp -P | $(CAKE_COMPILER) --target=arm8 --pancake --main_return=true > $@

ethernet_pnk.o: ethernet_pnk.S
	$(CC) -c -mcpu=$(CPU) $< -o $@

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

eth_driver.elf: ethernet_pnk.o imx/ethernet_pnk_c.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

imx/ethernet_pnk_c.o: ${ETHERNET_DRIVER_DIR}/ethernet_pnk.c ${CHECK_NETDRV_FLAGS_MD5}
	mkdir -p imx
	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER_DIR} -o $@ $<

# TODO: add new makefile var to build just the C file
# imx/ethernet.o: ${ETHERNET_DRIVER_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS_MD5}
#	mkdir -p imx
#	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER} -o $@ $<

-include imx/ethernet.d
