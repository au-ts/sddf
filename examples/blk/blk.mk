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
	CC := clang
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

# Allow to user to specify a custom partition
PARTITION :=
ifdef PARTITION
	PARTITION_ARG := --partition $(PARTITION)
endif

IMAGE_FILE := loader.img
REPORT_FILE  := report.txt
SYSTEM_FILE := blk.system

ifeq ($(strip $(MICROKIT_BOARD)), qemu_virt_aarch64)
	BLK_DRIVER_DIR := virtio
	CPU := cortex-a53
	QEMU := qemu-system-aarch64
	QEMU_ARCH_ARGS := -machine virt,virtualization=on -cpu cortex-a53 -device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_virt_riscv64)
	BLK_DRIVER_DIR := virtio
	QEMU := qemu-system-riscv64
	QEMU_ARCH_ARGS := -machine virt -kernel $(IMAGE_FILE)
else ifeq ($(strip $(MICROKIT_BOARD)), maaxboard)
	CPU := cortex-a53
	BLK_DRIVER_DIR := mmc/imx
	TIMER_DRIVER_DIR := imx
else
$(error Unsupported MICROKIT_BOARD given)
endif

DTC := dtc
PYTHON ?= python3

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug

TOP := ${SDDF}/examples/blk
CONFIGS_INCLUDE := ${TOP}

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
ARCH := ${shell grep 'CONFIG_SEL4_ARCH  ' $(BOARD_DIR)/include/kernel/gen_config.h | cut -d' ' -f4}

IMAGES := blk_driver.elf client.elf blk_virt.elf
CFLAGS := -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit \
		  -I$(CONFIGS_INCLUDE)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

ifeq ($(ARCH),aarch64)
	CFLAGS += -mcpu=$(CPU) -target aarch64-none-elf
else ifeq ($(ARCH),riscv64)
	CFLAGS += -march=rv64imafdc -target riscv64-none-elf
endif

DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
METAPROGRAM := $(TOP)/meta.py

BLK_DRIVER   := $(SDDF)/drivers/blk/${BLK_DRIVER_DIR}

BLK_COMPONENTS := $(SDDF)/blk/components

all: $(IMAGE_FILE)

include ${BLK_DRIVER}/blk_driver.mk

ifdef TIMER_DRIVER_DIR
include $(SDDF)/drivers/timer/$(TIMER_DRIVER_DIR)/timer_driver.mk
IMAGES += timer_driver.elf
endif

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
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE) $(PARTITION_ARG)
ifdef TIMER_DRIVER_DIR
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_blk_driver.data blk_driver.elf
endif
	$(OBJCOPY) --update-section .device_resources=blk_driver_device_resources.data blk_driver.elf
	$(OBJCOPY) --update-section .blk_driver_config=blk_driver.data blk_driver.elf
	$(OBJCOPY) --update-section .blk_virt_config=blk_virt.data blk_virt.elf
	$(OBJCOPY) --update-section .blk_client_config=blk_client_client.data client.elf

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu_disk:
	$(SDDF)/tools/mkvirtdisk disk 1 512 16777216

qemu: ${IMAGE_FILE} qemu_disk
	$(QEMU) $(QEMU_ARCH_ARGS) \
			-serial mon:stdio \
			-m size=2G \
			-nographic \
            -d guest_errors \
            -global virtio-mmio.force-legacy=false \
            -drive file=disk,if=none,format=raw,id=hd \
            -device virtio-blk-device,drive=hd

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
