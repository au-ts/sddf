#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
NET_DRIV_DIR := virtio
ETH_DRIV := eth_driver_virtio.elf
UART_DRIV_DIR := ns16550a
TIMER_DRIV_DIR := goldfish
QEMU := qemu-system-riscv64
QEMU_ARCH_ARGS := -machine virt -kernel $(IMAGE_FILE) -serial mon:stdio
