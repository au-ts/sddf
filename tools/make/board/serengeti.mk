#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

include ${SDDF}/drivers/i2c/opentitan/i2c_driver.mk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/ns16550a/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/ns16550a/serial_driver.mk
endif

include ${SDDF}/drivers/timer/apb_timer/timer_driver.mk
