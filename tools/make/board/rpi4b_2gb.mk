#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for Raspberry Pi 4b ith 1Gb RAM
# Should be included _before_ toolchain makefile.
# NET_DRIV_DIR :=
# ETH_DRIV := eth_driver_dwmac-5.10a.elf
UART_DRIV_DIR := ns16550a
TIMER_DRIV_DIR := bcm2835
#I2C_DRIV_DIR := ${PLATFORM}
CPU := cortex-a72
