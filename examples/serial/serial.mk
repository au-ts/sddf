#
# Copyright 2023, UNSW
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

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug

QEMU := qemu-system-aarch64

CC := clang
LD := ld.lld
AS := llvm-as
AR := llvm-ar
RANLIB := llvm-ranlib
OBJCOPY := llvm-objcopy
DTC := dtc
PYTHON ?= python3

MICROKIT_TOOL := $(MICROKIT_SDK)/bin/microkit

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	ARCH := aarch64
	DRIVER_DIR := meson
	CPU := cortex-a55
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_virt_aarch64)
	ARCH := aarch64
	DRIVER_DIR := arm
	CPU := cortex-a53
else ifeq ($(strip $(MICROKIT_BOARD)), maaxboard)
	ARCH := aarch64
	DRIVER_DIR := imx
	CPU := cortex-a53
else ifeq ($(strip $(MICROKIT_BOARD)), imx8mm_evk)
	ARCH := aarch64
	DRIVER_DIR := imx
	CPU := cortex-a53
else ifeq ($(strip $(MICROKIT_BOARD)), star64)
	ARCH := riscv64
	DRIVER_DIR := snps
else
$(error Unsupported MICROKIT_BOARD given)
endif

TOP := ${SDDF}/examples/serial
METAPROGRAM := $(TOP)/meta.py
UTIL := $(SDDF)/util
SERIAL_COMPONENTS := $(SDDF)/serial/components
UART_DRIVER := $(SDDF)/drivers/serial/$(DRIVER_DIR)
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SYSTEM_FILE := serial.system
DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb

IMAGES := uart_driver.elf \
	  client0.elf client1.elf \
	  serial_virt_tx.elf serial_virt_rx.elf
CFLAGS := -ffreestanding \
	  -g3 -O3 -Wall \
	  -Wno-unused-function -Werror \
	  -MD
LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

IMAGE_FILE = loader.img
REPORT_FILE = report.txt

ifeq ($(ARCH),aarch64)
	CFLAGS += -mcpu=$(CPU) -mstrict-align -target aarch64-none-elf
else ifeq ($(ARCH),riscv64)
	CFLAGS += -march=rv64imafdc -target riscv64-none-elf
endif
CFLAGS += -I$(BOARD_DIR)/include \
	-I${TOP}/include	\
	-I$(SDDF)/include \
	$(CFLAGS_ARCH)

CHECK_FLAGS_BOARD_MD5:=.board_cflags-$(shell echo -- ${CFLAGS} ${BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//')

${CHECK_FLAGS_BOARD_MD5}:
	-rm -f .board_cflags-*
	touch $@

${IMAGES}: libsddf_util_debug.a ${CHECK_FLAGS_BOARD_MD5}

include ${SDDF}/util/util.mk
include ${UART_DRIVER}/uart_driver.mk
include ${SERIAL_COMPONENTS}/serial_components.mk

%.elf: %.o
	${LD} -o $@ ${LDFLAGS} $< ${LIBS}

client.elf: client.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

client.o: ${TOP}/client.c ${CHECK_FLAGS_BOARD_MD5}
	$(CC) $(CFLAGS) -c -o $@ $<

client0.elf client1.elf: client.elf
	cp client.elf $@

$(DTB): $(DTS)
	dtc -q -I dts -O dtb $(DTS) > $(DTB)

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data uart_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data uart_driver.elf
	$(OBJCOPY) --update-section .serial_virt_rx_config=serial_virt_rx.data serial_virt_rx.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client0.data client0.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client1.data client1.elf

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	MICROKIT_SDK=${MICROKIT_SDK} $(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu: ${IMAGE_FILE}
	$(QEMU) -machine virt,virtualization=on -cpu cortex-a53 -serial mon:stdio -device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 -m size=2G -nographic


clean::
	${RM} -f *.elf
	find . -name '*.[od]' | xargs ${RM} -f

clobber:: clean
	${RM} -f ${IMAGE_FILE} ${REPORT_FILE}
