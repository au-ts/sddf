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
include ${SDDF}/blk/components/blk_components.mk

# I²C
include ${SDDF}/i2c/components/i2c_virt.mk
include ${SDDF}/i2c/libi2c.mk

# Network
include ${SDDF}/network/components/network_components.mk
include ${SDDF}/network/lib_sddf_lwip/lib_sddf_lwip.mk

# Serial
include ${SDDF}/serial/components/serial_components.mk
