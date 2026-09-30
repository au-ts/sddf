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
#  Expects libsddf_util_debug.a to be in LIBS

ETHERNET_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
CHECK_NETDRV_FLAGS_MD5:=.netdrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

ifeq ($(PANCAKE_NETWORK_DRIVER),1)
eth_driver.elf: ${BUILD_DIR}/ethernet_pnk.o imx/ethernet.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

ETHERNET_PNK = ${UTIL}/util.🥞 \
	${SDDF}/include/sddf/network/queue.🥞 \
	${ETHERNET_DRIVER_DIR}/ethernet.🥞

${BUILD_DIR}/ethernet_pnk.S: $(ETHERNET_PNK)
	cat $(ETHERNET_PNK) | cpp -P | $(CAKE_COMPILER) --target=arm8 --pancake --main_return=true > $@

imx/ethernet.o: ${ETHERNET_DRIVER_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS_MD5}
	mkdir -p imx
	${CC} -c ${CFLAGS} ${CFLAGS_network} -DPANCAKE_NETWORK_DRIVER -I ${ETHERNET_DRIVER_DIR} -o $@ $<

${BUILD_DIR}/ethernet_pnk.o: ${BUILD_DIR}/ethernet_pnk.S
ifeq ($(strip $(TOOLCHAIN)), clang)
	$(CC) -c -mcpu=$(CPU) -target $(TARGET) $< -o $@
else
	$(CC) -c -mcpu=$(CPU) $< -o $@
endif
else
eth_driver.elf: network/imx/ethernet.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@
endif

network/imx/ethernet.o: ${ETHERNET_DRIVER_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS_MD5}
	mkdir -p network/imx
	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER_DIR} -o $@ $<


-include imx/ethernet.d
