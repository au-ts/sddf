#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for i.MX8MP IOTGATE
# Should be included _before_ toolchain makefile.
PLATFORM := imx

I2C_DRIV_DIR := ${PLATFORM}
NET_DRIV_DIR := dwmac-5.10a
ETH_DRIV := eth_driver_${NET_DRIV_DIR}.elf
ETH_DRIV_DIR1 := imx
ETH_DRIV_1 := eth_driver_${ETH_DRIV_DIR1}.elf
TIMER_DRIV_DIR := ${PLATFORM}
UART_DRIV_DIR := ${PLATFORM}

CPU := cortex-a53
