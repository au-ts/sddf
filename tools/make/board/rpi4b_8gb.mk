#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for Raspberry Pi 4B ith 8GB RAM
# Should be included _before_ toolchain makefile.

UART_DRIV_DIR := ns16550a
TIMER_DRIV_DIR := bcm2835
CPU := cortex-a72
