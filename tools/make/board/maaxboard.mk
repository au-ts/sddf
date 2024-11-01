#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for the MAAXboard
# Should be included _before_ toolchain makefile.
PLATFORM := imx

BLK_DRIV_DIR := mmc/${PLATFORM}
I2C_DRIV_DIR := ${PLATFORM}
NET_DRIV_DIR := ${PLATFORM}
ETH_DRIV := eth_driver_${PLATFORM}.elf
TIMER_DRIV_DIR := ${PLATFORM}
UART_DRIV_DIR := ${PLATFORM}
CLK_DRIV_DIR := ${PLATFORM}
PWM_DRIV_DIR := imx
PINCTRL_DRIV_DIR := imx
TMU_DRIV_DIR := imx8mq
PMIC_DRIV_DIR := bd71837amwv
CLK_DRIV_DIR := ${PLATFORM}

CPU := cortex-a53
