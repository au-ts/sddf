#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
BLK_DRIV_DIR := virtio/mmio
GPU_DRIV_DIR := virtio
NET_DRIV_DIR := virtio/mmio
ETH_DRIV := eth_driver_virtio.elf
TIMER_DRIV_DIR := goldfish
UART_DRIV_DIR := ns16550a

QEMU := qemu-system-riscv64
QEMU_ARCH_ARGS := -machine virt \
					-kernel $(IMAGE_FILE) \
					-m size=2G \
					-serial mon:stdio

QEMU_NET_ARGS := -device virtio-net-device,netdev=netdev0

QEMU_BLK_ARGS := -device virtio-blk-device,drive=hd \
