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
	export GPIO_DRIVER_DIR := meson
	export CPU := cortex-a55
else
$(error Unsupported MICROKIT_BOARD given)
endif

TOP:= ${SDDF}/examples/gpio
METAPROGRAM := $(TOP)/meta.py
UTIL := $(SDDF)/util
GPIO_DRIVER := $(SDDF)/drivers/gpio/$(GPIO_DRIVER_DIR)
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SYSTEM_FILE := gpio.system
DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
# why does the i2c driver not have this -> i think we are only usign one ARCH currently 
# ARCH := ${shell grep 'CONFIG_SEL4_ARCH  ' $(BOARD_DIR)/include/kernel/gen_config.h | cut -d' ' -f4}

IMAGES := gpio_driver.elf client.elf
CFLAGS_ARCH := -mcpu=$(CPU) -mstrict-align -target aarch64-none-elf

# ifeq ($(ARCH),aarch64)
# 	CFLAGS_ARCH := -mcpu=$(CPU) -mstrict-align -target aarch64-none-elf
# else ifeq ($(ARCH),riscv64)
# 	CFLAGS_ARCH := -march=rv64imafdc -target riscv64-none-elf
# endif

# @ Tristan : may be able to not compile with the sib i got rid of this (-nostdlib \)
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
# @Trsitan: i dont think this is neccesary
# CHECK_FLAGS_BOARD_MD5:=.board_cflags-$(shell echo -- ${CFLAGS} ${MICROKIT_SDK} ${MICROKIT_BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//')

# ${CHECK_FLAGS_BOARD_MD5}:
# 	-rm -f .board_cflags-*
# 	touch $@

include ${GPIO_DRIVER}/gpio_driver.mk
include ${SDDF}/util/util.mk

${IMAGES}: libsddf_util_debug.a

# @Tristan: so it recompiles when the config file changes
-include client.d

client.o: ${TOP}/client.c
	$(CC) -c $(CFLAGS) $< -o client.o
client.elf: client.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

$(DTB): $(DTS)
	dtc -q -I dts -O dtb $(DTS) > $(DTB)

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=gpio_driver_device_resources.data gpio_driver.elf
	$(OBJCOPY) --update-section .gpio_client_config=gpio_client_client.data client.elf

$(IMAGE_FILE) $(REPORT_FILE): $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

# @ Tristan : i dont think this is neccesary
# qemu: $(IMAGE_FILE)
# 	$(QEMU) $(QEMU_ARCH_ARGS) \
# 			-serial mon:stdio \
# 			-m size=2G \
# 			-nographic \
# 			-d guest_errors

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
