#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This file transitively includes all the sDDF make files, to reduce makefile
# duplication.
#

ifeq ($(strip ${SDDF}),)
  $(error SDDF must be specified)
endif

ifeq ($(strip ${SDDF_LIBC_INCLUDE}),)
  ifeq ($(strip ${SDDF_CUSTOM_LIBC}),)
    $(error Either SDDF_LIBC_INCLUDE or SDDF_CUSTOM_LIBC must be set)
  endif
endif

# This defines the driver directories.
include ${SDDF}/tools/make/board/common.mk

# Utility Libraries
include ${SDDF}/util/util.mk
include ${SDDF}/benchmark/benchmark.mk

# Block
ifdef BLK_DRIV_DIR
  include ${SDDF}/drivers/blk/${BLK_DRIV_DIR}/blk_driver.mk
endif
include ${SDDF}/blk/components/blk_components.mk

# I²C
ifdef I2C_DRIV_DIR
  include ${SDDF}/drivers/i2c/${I2C_DRIV_DIR}/i2c_driver.mk
endif
include ${SDDF}/i2c/components/i2c_virt.mk
include ${SDDF}/i2c/libi2c.mk

# Network
ifdef NET_DRIV_DIR
  include ${SDDF}/drivers/network/${NET_DRIV_DIR}/eth_driver.mk
endif
ifdef ETH_DRIV_DIR1
  ifneq (${NET_DRIV_DIR},${ETH_DRIV_DIR1})
    include ${SDDF}/drivers/network/${ETH_DRIV_DIR1}/eth_driver.mk
  endif
endif
include ${SDDF}/network/components/network_components.mk
include ${SDDF}/network/lib_sddf_lwip/lib_sddf_lwip.mk

# Serial
ifdef UART_DRIV_DIR
  ifeq ($(PANCAKE_SERIAL_DRIVER),1)
    include ${SDDF}/drivers/serial/${UART_DRIV_DIR}/serial_driver_pnk.mk
  else
    include ${SDDF}/drivers/serial/${UART_DRIV_DIR}/serial_driver.mk
  endif
endif
include ${SDDF}/serial/components/serial_components.mk

# Timer
ifdef TIMER_DRIV_DIR
  include ${SDDF}/drivers/timer/${TIMER_DRIV_DIR}/timer_driver.mk
endif
