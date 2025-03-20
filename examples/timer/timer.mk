#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(SDDF)),)
$(error SDDF must be specified)
endif

BUILD_DIR ?= build
# By default we make a debug build so that the client debug prints can be seen.
MICROKIT_CONFIG ?= debug
IMAGE_FILE := loader.img
REPORT_FILE := report.txt

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
DTC := dtc
PYTHON ?= python3

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	export TIMER_DRIVER_DIR := meson
	export CPU := cortex-a55
else ifeq ($(strip $(MICROKIT_BOARD)), odroidc2)
	export TIMER_DRIVER_DIR := meson
	export CPU := cortex-a53
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_virt_aarch64)
	export TIMER_DRIVER_DIR := arm
	export CPU := cortex-a53
	export QEMU := qemu-system-aarch64
	export QEMU_ARCH_ARGS := -machine virt,virtualization=on -cpu cortex-a53 -device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_virt_riscv64)
	export TIMER_DRIVER_DIR := goldfish
	export QEMU := qemu-system-riscv64
	export QEMU_ARCH_ARGS := -machine virt -kernel $(IMAGE_FILE)
else ifeq ($(strip $(MICROKIT_BOARD)), star64)
	export TIMER_DRIVER_DIR := jh7110
else ifneq ($(filter $(strip $(MICROKIT_BOARD)),imx8mm_evk imx8mp_evk imx8mq_evk maaxboard),)
	export TIMER_DRIVER_DIR := imx
	export CPU := cortex-a53
else
$(error Unsupported MICROKIT_BOARD given)
endif

TOP:= ${SDDF}/examples/timer
METAPROGRAM := $(TOP)/meta.py
UTIL := $(SDDF)/util
TIMER_DRIVER := $(SDDF)/drivers/timer/$(TIMER_DRIVER_DIR)
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SYSTEM_FILE := timer.system
DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
ARCH := ${shell grep 'CONFIG_SEL4_ARCH  ' $(BOARD_DIR)/include/kernel/gen_config.h | cut -d' ' -f4}

IMAGES := timer_driver.elf client.elf

ifeq ($(ARCH),aarch64)
	CFLAGS_ARCH := -mcpu=$(CPU) -mstrict-align -target aarch64-none-elf
else ifeq ($(ARCH),riscv64)
	CFLAGS_ARCH := -march=rv64imafdc -target riscv64-none-elf
endif

CFLAGS := -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit \
		  $(CFLAGS_ARCH)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group


all: $(IMAGE_FILE)
CHECK_FLAGS_BOARD_MD5:=.board_cflags-$(shell echo -- ${CFLAGS} ${MICROKIT_BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//')

${CHECK_FLAGS_BOARD_MD5}:
	-rm -f .board_cflags-*
	touch $@

include ${TIMER_DRIVER}/timer_driver.mk
include ${SDDF}/util/util.mk

${IMAGES}: libsddf_util_debug.a

client.o: ${TOP}/client.c
	$(CC) -c $(CFLAGS) $< -o client.o
client.elf: client.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

$(DTB): $(DTS)
	dtc -q -I dts -O dtb $(DTS) > $(DTB)

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client.data client.elf

$(IMAGE_FILE) $(REPORT_FILE): $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu: $(IMAGE_FILE)
	$(QEMU) $(QEMU_ARCH_ARGS) \
			-serial mon:stdio \
			-m size=2G \
			-nographic \
			-d guest_errors

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
