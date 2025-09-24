#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
PLATFORM := arm
NET_DRIV_DIR := virtio
ETH_DRIV := eth_driver_virtio.elf
UART_DRIV_DIR := ${PLATFORM}
TIMER_DRIV_DIR := ${PLATFORM}
BLK_DRIV_DIR := virtio
CPU := cortex-a53
QEMU := qemu-system-aarch64
QEMU_ARCH_ARGS := -machine virt,virtualization=on -cpu cortex-a53 \
		  -device loader,file=\$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
		  -serial mon:stdio
