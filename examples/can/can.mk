#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

METAPROGRAM := $(TOP)/meta.py

BUILD_DIR ?= build
# By default we make a debug build so that the client debug prints can be seen.
MICROKIT_CONFIG ?= debug

DTC := dtc
QEMU := qemu-system-aarch64
PYTHON ?= python3

CC := clang
LD := ld.lld
AR := llvm-ar
AS := clang
ASFLAGS := -c -x assembler-with-cpp -target aarch64-none-elf
RANLIB := llvm-ranlib
OBJCOPY := llvm-objcopy

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
UTIL := $(SDDF)/util

IMAGES := can_driver.elf pinctrl_driver.elf client.elf

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
		  -I$(SDDF)/include/microkit \
		  -I$(SDDF)/include/ \
		  $(CFLAGS_ARCH)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

IMAGE_FILE := loader.img
DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
SYSTEM_FILE := can.system
REPORT_FILE := report.txt
CLIENT_OBJS := client.o
CAN_DRIVER := $(SDDF)/drivers/network/$(CAN_DRIVER_DIR)
PINCTRL_DRIVER := ${SDDF}/drivers/pinctrl/${PINCTRL_DRIVER_DIR}

all: $(IMAGE_FILE)
CHECK_FLAGS_BOARD_MD5:=.board_cflags-$(shell echo -- ${CFLAGS} ${MICROKIT_BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//')

${CHECK_FLAGS_BOARD_MD5}:
	-rm -f .board_cflags-*
	touch $@

# pinctrl specific makefile variables
DTS_FILE = $(DTS)
PINMUX_DEVICE = pinctrl
SOC = imx8mp-evk

include ${CAN_DRIVER}/can_driver.mk
include ${PINCTRL_DRIVER}/pinctrl_driver.mk
include ${}
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
	# $(OBJCOPY) --update-section .device_resources=can_driver_device_resources.data can_driver.elf

# $(OBJCOPY) --update-section .can_client_config=can_client_client.data client.elf

$(IMAGE_FILE) $(REPORT_FILE): $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu: $(IMAGE_FILE)
	$(QEMU) -machine virt,virtualization=on \
			-cpu cortex-a53 \
			-serial mon:stdio \
			-device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
			-m size=2G \
			-nographic

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
