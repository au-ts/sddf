#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

CPU := cortex-a53
QEMU := qemu-system-aarch64
QEMU_ARCH_ARGS := -machine virt,virtualization=on -cpu cortex-a53 \
			-m size=2G \
			-serial mon:stdio \
			-global virtio-mmio.force-legacy=false \
			-device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0

QEMU_NET_ARGS ?= -device virtio-net-device,netdev=netdev0,bus=virtio-mmio-bus.0

QEMU_BLK_ARGS ?= -device virtio-blk-device,drive=hd,bus=virtio-mmio-bus.1

include ${SDDF}/drivers/blk/virtio/mmio/blk_driver.mk

include ${SDDF}/drivers/gpu/virtio/gpu_driver.mk

ETH_DRIV := eth_driver_virtio.elf
ETH_DRIV_1 := eth_driver_virtio.elf
include ${SDDF}/drivers/network/virtio/mmio/eth_driver.mk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/arm/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/arm/serial_driver.mk
endif

include ${SDDF}/drivers/timer/arm/timer_driver.mk
