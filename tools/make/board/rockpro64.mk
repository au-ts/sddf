#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for rockpro64
# Should be included _before_ toolchain makefile.
# WARNING: not fully working yet
PLATFORM := rk3399

I2C_DRIV_DIR := ${PLATFORM}
NET_DRIV_DIR := dwmac-5.10a
ETH_DRIV := eth_driver_dwmac-5.10a.elf
#TIMER_DRIV_DIR := arm
UART_DRIV_DIR := ns16550a

CPU := cortex-a72
