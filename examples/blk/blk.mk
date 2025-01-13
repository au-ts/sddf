#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile is copied into the build directory
# and operated on from there.
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(SDDF)),)
$(error SDDF must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := clang
endif

ifeq ($(strip $(TOOLCHAIN)), clang)
	CC := clang -target aarch64-none-elf
	LD := ld.lld
	AR := llvm-ar
	RANLIB := llvm-ranlib
	OBJCOPY := llvm-objcopy
else
	CC := $(TOOLCHAIN)-gcc
	LD := $(TOOLCHAIN)-ld
	AS := $(TOOLCHAIN)-as
	AR := $(TOOLCHAIN)-ar
	RANLIB := $(TOOLCHAIN)-ranlib
	OBJCOPY := $(TOOLCHAIN)-objcopy
endif

DTC := dtc
QEMU := qemu-system-aarch64
PYTHON ?= python3

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug

BLK_DRIVER_DIR := virtio
CPU := cortex-a53

TOP := ${SDDF}/examples/blk
CONFIGS_INCLUDE := ${TOP}

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)

IMAGES := blk_driver.elf client.elf blk_virt.elf
CFLAGS := -mcpu=$(CPU) \
		  -mstrict-align \
		  -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -I$(CONFIGS_INCLUDE)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

IMAGE_FILE   := loader.img
REPORT_FILE  := report.txt
SYSTEM_FILE := blk.system
DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
METAPROGRAM := $(TOP)/meta.py

BLK_DRIVER   := $(SDDF)/drivers/blk/${BLK_DRIVER_DIR}

BLK_COMPONENTS := $(SDDF)/blk/components

all: $(IMAGE_FILE)

include ${BLK_DRIVER}/blk_driver.mk

include ${SDDF}/util/util.mk
include ${BLK_COMPONENTS}/blk_components.mk

${IMAGES}: libsddf_util_debug.a

client.o: ${TOP}/client.c ${TOP}/basic_data.h
	$(CC) -c $(CFLAGS) -I. $< -o client.o
client.elf: client.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

$(DTB): $(DTS)
	dtc -q -I dts -O dtb $(DTS) > $(DTB)

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=blk_driver_device_resources.data blk_driver.elf
	$(OBJCOPY) --update-section .blk_driver_config=blk_driver.data blk_driver.elf
	$(OBJCOPY) --update-section .blk_virt_config=blk_virt.data blk_virt.elf
	$(OBJCOPY) --update-section .blk_client_config=blk_client_client.data client.elf

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu_disk:
	$(SDDF)/tools/mkvirtdisk mydisk 1 512 16777216

qemu: ${IMAGE_FILE} qemu_disk
	$(QEMU) -machine virt,virtualization=on \
			-cpu cortex-a53 \
			-serial mon:stdio \
			-device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
			-m size=2G \
			-nographic \
            -global virtio-mmio.force-legacy=false \
            -d guest_errors \
            -drive file=mydisk,if=none,format=raw,id=hd \
            -device virtio-blk-device,drive=hd

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
