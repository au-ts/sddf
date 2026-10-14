#
# Copyright 2026, Skykraft
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for kria_k26
# Should be included _before_ toolchain makefile.

CPU := cortex-a53

ETH_DRIV := eth_driver_znyqmp_gem.elf
include ${SDDF}/drivers/network/zynqmp-gem/eth_driver.mk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/zynqmp/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/zynqmp/serial_driver.mk
endif

include ${SDDF}/drivers/timer/cdns/timer_driver.mk
