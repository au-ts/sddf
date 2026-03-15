#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for the x86_64_generic
# Should be included _before_ toolchain makefile.

BLK_DRIV_DIR ?= virtio/pci
NET_DRIV_DIR ?= virtio/pci
ETH_DRIV ?= eth_driver_virtio.elf
TIMER_DRIV_DIR ?= hpet
UART_DRIV_DIR ?= pc99

CPU := generic

SEL4_64B := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)/elf/sel4.elf
SEL4_32B := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)/elf/sel4_32.elf

QEMU := qemu-system-x86_64
QEMU_ARCH_ARGS := -machine q35 \
		-kernel $(SEL4_32B) \
		-m size=2G \
		-serial mon:stdio \
		-cpu qemu64,+fsgsbase,+pdpe1gb,+pcid,+invpcid,+xsave,+xsaves,+xsaveopt \
		-initrd $(IMAGE_FILE)

# The PCI slot is hard-coded in the virtIO drivers for now, so we have to
# specify the slot with QEMU as well.
# See https://github.com/au-ts/sddf/issues/607 for details.
QEMU_NET_ARGS ?= -device virtio-net-pci,netdev=netdev0,addr=0x2.0
QEMU_BLK_ARGS ?= -device virtio-blk-pci,drive=hd,addr=0x3.0
