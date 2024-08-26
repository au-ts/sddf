#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for IMX8MQ_evk
# Should be included _before_ toolchain makefile.
PLATFORM := imx
NET_DRIV_DIR := ${PLATFORM}
ETH_DRIV := eth_driver_${PLATFORM}.elf
ETH_DRIV_DIR1 := dwmac-5.10a
ETH_DRIV_1 := eth_driver_dwmac-5.10a.elf
UART_DRIV_DIR := ${PLATFORM}
TIMER_DRIV_DIR := ${PLATFORM}
I2C_DRIV_DIR := ${PLATFORM}
CPU := cortex-a53
BLK_DRIV_DIR := mmc/imx
