#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for Odroid C4
# Should be included _before_ toolchain makefile.

CPU := cortex-a55

include ${SDDF}/drivers/i2c/meson/i2c_driver.mk

ETH_DRIV := eth_driver_meson.elf
include ${SDDF}/drivers/network/meson/eth_driver.mk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/meson/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/meson/serial_driver.mk
endif

include ${SDDF}/drivers/timer/meson/timer_driver.mk
