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
	TOOLCHAIN := aarch64-none-elf
endif

ifeq ($(strip $(TOOLCHAIN)), clang)
	CC := clang -target aarch64-none-elf
	LD := ld.lld
	AR := llvm-ar
	RANLIB := llvm-ranlib
else
	CC := $(TOOLCHAIN)-gcc
	LD := $(TOOLCHAIN)-ld
	AS := $(TOOLCHAIN)-as
	AR := $(TOOLCHAIN)-ar
	RANLIB := $(TOOLCHAIN)-ranlib
endif

QEMU := qemu-system-aarch64

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug

TIMER_DRIVER_DIR := arm

TOP := ${SDDF}/examples/blk
CONFIGS_INCLUDE := ${TOP}

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)

IMAGES := client.elf blk_virt.elf

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	IMAGES += sdmmc_driver.elf
	BLK_DRIVER_DIR := sdmmc
	BLK_DRIVER_MK := sdmmc_driver.mk
	CPU := cortex-a53
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_virt_aarch64)
	IMAGES += blk_driver.elf
	BLK_DRIVER_DIR := virtio
	BLK_DRIVER_MK := blk_driver.mk
	CPU := cortex-a53
	QEMU := qemu-system-aarch64
else
	$(error Unsupported MICROKIT_BOARD given)
endif

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
SYSTEM_FILE  := ${TOP}/board/$(MICROKIT_BOARD)/blk.system

BLK_DRIVER   := $(SDDF)/drivers/blk/${BLK_DRIVER_DIR}
TIMER_DRIVER := $(SDDF)/drivers/timer/${TIMER_DRIVER_DIR}

BLK_COMPONENTS := $(SDDF)/blk/components

all: $(IMAGE_FILE)

include ${BLK_DRIVER}/$(BLK_DRIVER_MK)
include ${TIMER_DRIVER}/timer_driver.mk

include ${SDDF}/util/util.mk
include ${BLK_COMPONENTS}/blk_components.mk

${IMAGES}: libsddf_util_debug.a

basic_data.h: ${TOP}/basic_data.txt
	xxd -n basic_data -i ${TOP}/basic_data.txt > basic_data.h

client.o: ${TOP}/client.c basic_data.h
	$(CC) -c $(CFLAGS) -I. $< -o client.o
client.elf: client.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu_disk:
	../mkvirtdisk mydisk 1 512 16777216

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
