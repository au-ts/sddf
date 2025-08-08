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

ifeq ($(strip $(LIBMICROKITCO_PATH)),)
$(error LIBMICROKITCO_PATH must be specified)
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

ifeq ($(strip $(MICROKIT_BOARD)), cheshire)
	SPI_DRIVER_DIR := opentitan
else
$(error Unsupported MICROKIT_BOARD given)
endif
BOARD := $(MICROKIT_BOARD)
#TODO: this is a workaround to deal with libmicrokitco
CPU := medany
LIBMICROKITCO_INCLUDE_DIR := $(LIBMICROKITCO_PATH)
LIBMICROKITCO_OPTS_DIR := $(SDDF)/include/sddf/spi
LIBMICROKITCO_OPT_PATH := $(LIBMICROKITCO_OPTS_DIR)
LIBMICROKITCO_OBJ := libmicrokitco.a

LLVM := 1
TOP:= ${SDDF}/examples/spi
METAPROGRAM := $(TOP)/meta.py
UTIL := $(SDDF)/util
SPI := $(SDDF)/spi
SPI_DRIVER := $(SDDF)/drivers/spi/$(SPI_DRIVER_DIR)
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SYSTEM_FILE := spi.system
DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
ARCH := ${shell grep 'CONFIG_SEL4_ARCH  ' $(BOARD_DIR)/include/kernel/gen_config.h | cut -d' ' -f4}

IMAGES := spi_driver.elf spi_virt.elf client.elf

ifeq ($(ARCH),aarch64)
	TARGET := aarch64-none-elf
	CFLAGS_ARCH := -mcpu=$(CPU) -mstrict-align -target $(TARGET)
else ifeq ($(ARCH),riscv64)
	TARGET := riscv64-none-elf
	CFLAGS_ARCH := -march=rv64imafdc -target $(TARGET)
endif

CFLAGS := -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit \
		  -I$(LIBMICROKITCO_PATH) \
		  -std=gnu23 \
		  $(CFLAGS_ARCH)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

all: $(IMAGE_FILE)
CHECK_FLAGS_BOARD_MD5:=.board_cflags-$(shell echo -- ${CFLAGS} ${MICROKIT_SDK} ${MICROKIT_BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//')

${CHECK_FLAGS_BOARD_MD5}:
	-rm -f .board_cflags-*
	touch $@

export LIBMICROKITCO_PATH LIBMICROKITCO_OPT_PATH TARGET MICROKIT_SDK BUILD_DIR MICROKIT_BOARD MICROKIT_CONFIG CPU LLVM

libmicrokitco/$(LIBMICROKITCO_OBJ):
	make -f $(LIBMICROKITCO_PATH)/Makefile

include ${SPI_DRIVER}/spi_driver.mk
include ${SDDF}/util/util.mk
include ${SDDF}/spi/components/spi_virt.mk
include ${SPI}/libspi.mk
include ${SDDF}/spi/devices/w25qxx/w25qxx.mk

${IMAGES}: libsddf_util_debug.a

# TODO: relocate libmicrokitco_opts.h, as it is currently stored in include/sddf/spi and there is an
# additional include path specified here
client.o: ${TOP}/client.c
	$(CC) -c -I$(SDDF)/include/sddf/spi $(CFLAGS) $< -o client.o
client.elf: client.o libspi.a libmicrokitco/$(LIBMICROKITCO_OBJ) w25qxx.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(DTB): $(DTS)
	dtc -q -I dts -O dtb $(DTS) > $(DTB)

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB) spi_virt.elf client.elf spi_driver.elf
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --output . --sdf $(SYSTEM_FILE) --dtb $(DTB)
	$(OBJCOPY) --update-section .spi_virt_config=spi_virt.data spi_virt.elf
	$(OBJCOPY) --update-section .spi_client_config=spi_client_spi_client.data client.elf
	$(OBJCOPY) --update-section .spi_driver_config=spi_driver.data spi_driver.elf
	$(OBJCOPY) --update-section .device_resources=spi_driver_device_resources.data spi_driver.elf

$(IMAGE_FILE) $(REPORT_FILE): $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

clean::
	rm -f *.o *.elf
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
