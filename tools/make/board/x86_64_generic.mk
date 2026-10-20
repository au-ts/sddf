#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for the x86_64_generic
# Should be included _before_ toolchain makefile.

CPU := generic

UART_DRIV_DIR ?= pc99
ifeq (${X86_BOARD},qemu_virt_x86)
    BLK_DRIV_DIR ?= virtio/pci
    NET_DRIV_DIR ?= virtio/pci
else
    BLK_DRIV_DIR ?= nvme
    NET_DRIV_DIR ?= ixgbe
endif

# The PCI slot is hard-coded in the virtIO drivers for now, so we have to
# specify the slot with QEMU as well.
# See https://github.com/au-ts/sddf/issues/607 for details.
QEMU_NET_ARGS ?= -device virtio-net-pci,netdev=netdev0,addr=0x2.0
QEMU_BLK_ARGS ?= -device virtio-blk-pci,drive=hd,addr=0x3.0

include ${SDDF}/drivers/acpi/acpi_driver.mk
include ${SDDF}/drivers/pcie/pcie_driver.mk

include ${SDDF}/drivers/blk/${BLK_DRIV_DIR}/blk_driver.mk

include ${SDDF}/drivers/network/${NET_DRIV_DIR}/eth_driver.mk

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
  include ${SDDF}/drivers/serial/${UART_DRIV_DIR}/serial_driver_pnk.mk
else
  include ${SDDF}/drivers/serial/${UART_DRIV_DIR}/serial_driver.mk
endif

include ${SDDF}/drivers/timer/tsc_hpet/timer_driver.mk
