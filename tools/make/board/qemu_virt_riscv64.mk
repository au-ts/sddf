#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

QEMU := qemu-system-riscv64
QEMU_ARCH_ARGS := -machine virt \
					-kernel $(IMAGE_FILE) \
					-m size=2G \
					-serial mon:stdio \
				    -global virtio-mmio.force-legacy=false

QEMU_NET_ARGS ?= -device virtio-net-device,netdev=netdev0,bus=virtio-mmio-bus.0

QEMU_BLK_ARGS ?= -device virtio-blk-device,drive=hd,bus=virtio-mmio-bus.1

include ${SDDF}/drivers/blk/virtio/mmio/blk_driver.mk

include ${SDDF}/drivers/gpu/virtio/gpu_driver.mk

ETH_DRIV := eth_driver_virtio.elf
include ${SDDF}/drivers/network/virtio/mmio/eth_driver.mk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/ns16550a/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/ns16550a/serial_driver.mk
endif

include ${SDDF}/drivers/timer/goldfish/timer_driver.mk
