#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
PLATFORM := arm

BLK_DRIV_DIR := virtio
GPU_DRIV_DIR := virtio
NET_DRIV_DIR := virtio
ETH_DRIV := eth_driver_virtio.elf
ETH_DRIV_DIR1 := ${NET_DRIV_DIR}
ETH_DRIV_1 := ${ETH_DRIV}
TIMER_DRIV_DIR := ${PLATFORM}
UART_DRIV_DIR := ${PLATFORM}

CPU := cortex-a53
QEMU := qemu-system-aarch64
QEMU_ARCH_ARGS := -machine virt,virtualization=on -cpu cortex-a53 \
		  -m size=2G \
		  -device loader,file=\$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
		  -serial mon:stdio
