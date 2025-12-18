#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the VirtIO driver
#
# NOTES:
#   Generates eth_driver.elf
#   Assumes libsddf_util_debug.a is in LIBS

ETHERNET_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

CHECK_NETDRV_FLAGS_MD5:=.netdrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETDRV_FLAGS_MD5}:
	-rm -f .netdrv_cflags-*
	touch $@

ifeq ($(PANCAKE_NETWORK_DRIVER),1)
eth_driver.elf: ${BUILD_DIR}/ethernet_pnk.o virtio/ethernet.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

ETHERNET_PNK = ${UTIL}/util.pnk \
		${SDDF}/include/sddf/network/queue.pnk \
		${ETHERNET_DRIVER_DIR}/ethernet.pnk

${BUILD_DIR}/ethernet_pnk.S: $(ETHERNET_PNK)
ifeq ($(findstring riscv,$(MICROKIT_BOARD)),riscv)
	cat $(ETHERNET_PNK) | cpp -P | $(CAKE_COMPILER) --target=riscv --pancake --main_return=true > $@
else
	cat $(ETHERNET_PNK) | cpp -P | $(CAKE_COMPILER) --target=arm8 --pancake --main_return=true > $@
endif

virtio/ethernet.o: ${ETHERNET_DRIVER_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS_MD5}
	mkdir -p virtio
	${CC} -c ${CFLAGS} ${CFLAGS_network} -DPANCAKE_NETWORK_DRIVER -I ${ETHERNET_DRIVER_DIR} -o $@ $<

${BUILD_DIR}/ethernet_pnk.o: ${BUILD_DIR}/ethernet_pnk.S
ifeq ($(findstring riscv,$(MICROKIT_BOARD)),riscv)
	$(CC) -c -march=rv64imafdc -target riscv64-none-elf $< -o $@
else
	$(CC) -c -mcpu=$(CPU) -target $(TARGET) $< -o $@
endif
else
eth_driver.elf: network/virtio/ethernet.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@
endif

network/virtio/ethernet.o: ${ETHERNET_DRIVER_DIR}/ethernet.c ${CHECK_NETDRV_FLAGS_MD5}
	mkdir -p network/virtio
	${CC} -c ${CFLAGS} ${CFLAGS_network} -I ${ETHERNET_DRIVER_DIR} -o $@ $<

-include virtio/ethernet.d
