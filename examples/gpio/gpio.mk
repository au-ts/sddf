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
	export TIMER_DRIVER_DIR := meson
	export CPU := cortex-a55
else ifeq ($(strip $(MICROKIT_BOARD)), maaxboard)
	export GPIO_DRIVER_DIR := imx
	export TIMER_DRIVER_DIR := imx
	export CPU := cortex-a55
else
$(error Unsupported MICROKIT_BOARD given)
endif

TOP:= ${SDDF}/examples/gpio
METAPROGRAM := $(TOP)/meta.py
UTIL := $(SDDF)/util
LIBCO := $(SDDF)/libco
TIMER_DRIVER := $(SDDF)/drivers/timer/$(TIMER_DRIVER_DIR)
GPIO_DRIVER := $(SDDF)/drivers/gpio/$(GPIO_DRIVER_DIR)
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SYSTEM_FILE := gpio.system
DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
CONFIGS_DIR   := $(TOP)/include
CONFIG_HEADER := $(CONFIGS_DIR)/gpio_config.h

IMAGES := gpio_driver.elf timer_driver.elf client.elf
CFLAGS_ARCH := -mcpu=$(CPU) -mstrict-align -target aarch64-none-elf

CFLAGS := -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit \
		  -I$(LIBCO) \
		  -I$(CONFIGS_DIR) \
		  $(CFLAGS_ARCH)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group


all: $(IMAGE_FILE)
CHECK_FLAGS_BOARD_MD5:=.board_cflags-$(shell echo -- ${CFLAGS} ${MICROKIT_SDK} ${MICROKIT_BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//')

${CHECK_FLAGS_BOARD_MD5}:
	-rm -f .board_cflags-*
	touch $@

include ${TIMER_DRIVER}/timer_driver.mk
include ${GPIO_DRIVER}/gpio_driver.mk
include ${SDDF}/util/util.mk
include ${LIBCO}/libco.mk

${IMAGES}: libsddf_util_debug.a

# So client recompiles when the config file changes
-include client.d

client.o: ${TOP}/client.c $(CONFIG_HEADER)
	$(CC) -c $(CFLAGS) $< -o client.o
client.elf: client.o libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o client.elf

$(DTB): $(DTS)
	dtc -q -I dts -O dtb $(DTS) > $(DTB)

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=gpio_driver_device_resources.data gpio_driver.elf
	$(OBJCOPY) --update-section .gpio_client_config=gpio_client_client.data client.elf
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client.data client.elf


$(IMAGE_FILE) $(REPORT_FILE): $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
