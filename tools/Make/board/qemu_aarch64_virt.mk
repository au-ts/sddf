#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
PLATFORM := arm
NET_DRIV_DIR := virtio
UART_DRIV_DIR ?= ${PLATFORM}
TIMER_DRIV_DIR := ${PLATFORM}
TRIPLE := aarch64-none-elf
CPU ?= cortex-a53
QEMU := qemu-system-aarch64
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
