#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for the MAAXboard
# Should be included _before_ toolchain makefile.
PLATFORM := imx
NET_DRIV_DIR := ${PLATFORM}
UART_DRIV_DIR := ${PLATFORM}
TIMER_DRIV_DIR := ${PLATFORM}
I2C_DRIV_DIR := ${PLATFORM}
CPU := cortex-a53
