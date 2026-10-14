#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for rockpro64
# Should be included _before_ toolchain makefile.
# WARNING: not fully working yet

CPU := cortex-a53

ETH_DRIV := eth_driver_meson.elf
include ${SDDF}/drivers/network/meson/eth_driver.mk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/ns16550a/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/ns16550a/serial_driver.mk
endif

include ${SDDF}/drivers/timer/rk3399/timer_driver.mk
