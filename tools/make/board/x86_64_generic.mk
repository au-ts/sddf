#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Set up variables for the x86_64_generic
# Should be included _before_ toolchain makefile.

BLK_DRIV_DIR :=
I2C_DRIV_DIR :=
NET_DRIV_DIR := virtio/pci
ETH_DRIV :=
TIMER_DRIV_DIR := hpet
UART_DRIV_DIR := pc99

CPU := generic

SEL4_64B := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)/elf/sel4.elf
SEL4_32B := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)/elf/sel4_32.elf

QEMU := qemu-system-x86_64
QEMU_ARCH_ARGS = -machine q35 \
				-cpu qemu64,+fsgsbase,+pdpe1gb,+pcid,+invpcid,+xsave,+xsaves,+xsaveopt \
				-kernel $(SEL4_32B) \
				-initrd $(IMAGE_FILE)
