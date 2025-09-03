#
# Copyright 2025, UNSW
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
SYSTEM_FILE := dvfs.system

ifeq ($(strip $(MICROKIT_BOARD)), zcu102)
	CPU := cortex-a53
	SERIAL_DRIVER_DIR := zynqmp
	TIMER_DRIVER_DIR := cdns
else
$(error Unsupported MICROKIT_BOARD given)
endif

DTC := dtc
PYTHON ?= python3

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug

TOP := ${SDDF}/examples/dvfs
CONFIGS_INCLUDE := ${TOP}

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
ARCH := ${shell grep 'CONFIG_SEL4_ARCH  ' $(BOARD_DIR)/include/kernel/gen_config.h | cut -d' ' -f4}
SDDF_CUSTOM_LIBC := 1

IMAGES := dvfs.elf serial_virt_tx.elf serial_driver.elf timer_driver.elf idle.elf
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

SERIAL_DRIVER := $(SDDF)/drivers/serial/${SERIAL_DRIVER_DIR}

all: $(IMAGE_FILE)

include ${SDDF}/drivers/serial/${SERIAL_DRIVER_DIR}/serial_driver.mk
include ${SDDF}/drivers/timer/${TIMER_DRIVER_DIR}/timer_driver.mk

include ${SDDF}/util/util.mk
include ${SDDF}/serial/components/serial_components.mk

${IMAGES}: libsddf_util_debug.a

microkit_sdk_config_dir := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
sel4_include_dirs := $(microkit_sdk_config_dir)/include

idle.elf: ${SDDF}/examples/dvfs/idle.c
	$(CC) -c $(CFLAGS) -I. $< -o idle.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

helper.o: ${SDDF}/examples/dvfs/src/helper.c
	$(CC) -c $(CFLAGS) $< -o $@

libhelper.a: helper.o
	${AR} rcs $@ $<

dvfs.elf: libhelper.a
	@echo "Building dvfs.elf for board $(MICROKIT_BOARD)..." && \
	echo "MICROKIT SDK config directory: $(microkit_sdk_config_dir)" && \
	echo "SEl4 include directories: $(sel4_include_dirs)" && \
	cd .. && \
	SEL4_INCLUDE_DIRS=$(abspath $(sel4_include_dirs)) \
	RUSTFLAGS="-L $(BUILD_DIR)/ -l static=helper" \
	cargo build \
		-Z build-std=core,alloc,compiler_builtins \
		-Z build-std-features=compiler-builtins-mem \
		--target-dir $(BUILD_DIR) \
		--target support/targets/aarch64-sel4-microkit-minimal.json
	@echo "Build complete: $(TARGET_ELF)"
	cp ./aarch64-sel4-microkit-minimal/debug/dvfs.elf $(BUILD_DIR)

$(DTB): $(DTS)
	dtc -q -I dts -O dtb $(DTS) > $(DTB)

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE) $(PARTITION_ARG)
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_blk_driver.data dvfs.elf
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client.data dvfs.elf

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)
