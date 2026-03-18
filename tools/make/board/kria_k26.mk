#
# Copyright 2026, Skykraft
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for kria_k26
# Should be included _before_ toolchain makefile.
PLATFORM := zynqmp
NET_DRIV_DIR := zynqmp-gem
ETH_DRIV := eth_driver_znyqmp_gem.elf
TIMER_DRIV_DIR := cdns
UART_DRIV_DIR := ${PLATFORM}

CPU := cortex-a53
