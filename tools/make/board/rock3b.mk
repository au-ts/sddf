#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause

CPU := cortex-a55

ETH_DRIV := eth_driver_dwmac-5.10a.elf
ETH_DRIV_1 := eth_driver_dwmac-5.10a.elf
include ${SDDF}/drivers/network/dwmac-5.10a/eth_driver.mk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/ns16550a/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/ns16550a/serial_driver.mk
endif

include ${SDDF}/drivers/timer/rk3568/timer_driver.mk
