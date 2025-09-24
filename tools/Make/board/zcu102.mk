#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for zcu102
# Should be included _before_ toolchain makefile.
PLATFORM := zynqmp
# NET_DRIV_DIR :=
# ETH_DRIV := eth_driver_dwmac-5.10a.elf
UART_DRIV_DIR := ${PLATFORM}
TIMER_DRIV_DIR := cdns
#I2C_DRIV_DIR := ${PLATFORM}
CPU := cortex-a53
