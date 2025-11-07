#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause

PLATFORM := rk3568
# Placeholders
#I2C_DRIV_DIR :=
NET_DRIV_DIR := dwmac-5.10a
ETH_DRIV := eth_driver_dwmac-5.10a.elf
UART_DRIV_DIR := ns16550a
TIMER_DRIV_DIR := ${PLATFORM}

CPU := cortex-a55
