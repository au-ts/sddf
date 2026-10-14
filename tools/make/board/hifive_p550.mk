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
