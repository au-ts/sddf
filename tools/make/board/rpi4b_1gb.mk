#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for Raspberry Pi 4b ith 1Gb RAM
# Should be included _before_ toolchain makefile.

CPU := cortex-a72

ETH_DRIV := eth_driver_genet.elf
include ${SDDF}/drivers/network/genet/eth_driver.mk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/ns16550a/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/ns16550a/serial_driver.mk
endif

include ${SDDF}/drivers/timer/bcm2835/timer_driver.mk
