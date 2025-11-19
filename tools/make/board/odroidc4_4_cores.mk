#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for SMP Odroid C4
# Should be included _before_ toolchain makefile.
PLATFORM := meson

I2C_DRIV_DIR := ${PLATFORM}
NET_DRIV_DIR := ${PLATFORM}
ETH_DRIV := eth_driver_meson.elf
TIMER_DRIV_DIR := ${PLATFORM}
UART_DRIV_DIR := ${PLATFORM}

CPU := cortex-a55

# Temporary fix to allow the non SMP dts/dtb to be used
DTS := $(SDDF)/dts/odroidc4.dts
DTB := odroidc4.dtb
