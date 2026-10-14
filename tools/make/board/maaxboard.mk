#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for the MAAXboard
# Should be included _before_ toolchain makefile.

CPU := cortex-a53

include ${SDDF}/drivers/blk/mmc/imx/blk_driver.mk

ETH_DRIV := eth_driver_imx.elf
include ${SDDF}/drivers/network/imx/eth_driver.mk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/imx/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/imx/serial_driver.mk
endif

include ${SDDF}/drivers/timer/imx/timer_driver.mk
