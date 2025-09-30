#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/ns16550a/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/ns16550a/serial_driver.mk
endif
include ${SDDF}/drivers/timer/eswin/timer_driver.mk
#NET_DRIV_DIR := dwmac-5.10a
#ETH_DRIV := eth_driver_dwmac-5.10a.elf
