#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for Odroid C4
# Should be included _before_ toolchain makefile.
PLATFORM := meson
NET_DRIV_DIR := ${PLATFORM}
ETH_DRIV := eth_driver_meson.elf
UART_DRIV_DIR := ${PLATFORM}
TIMER_DRIV_DIR := ${PLATFORM}
I2C_DRIV_DIR := ${PLATFORM}
CPU := cortex-a55
TRIPLE := aarch64-none-elf
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
