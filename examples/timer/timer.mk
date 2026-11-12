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

SUPPORTED_BOARDS := \
			imx8mm_evk \
			imx8mp_evk \
			imx8mq_evk \
			imx8mp_iotgate \
			kria_k26 \
			maaxboard \
			odroidc2 \
			odroidc4 \
			qemu_virt_aarch64 \
			qemu_virt_riscv64 \
			rock3b \
			rockpro64 \
			rpi4b_1gb \
			serengeti \
			star64 \
			zcu102 \
			x86_64_generic \
			x86_64_generic_vtx

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := clang
endif

SDDF_CUSTOM_LIBC := 1
include ${SDDF}/tools/make/sddf.mk

TOP := ${SDDF}/examples/timer
METAPROGRAM := $(TOP)/meta.py
SYSTEM_FILE := timer.system

IMAGES := timer_driver.elf timer_virt.elf client.elf

ifeq ($(MULTIKERNEL),1)
MULTIKERNEL_CONFIG ?= $(TOP)/partitions.json
include ${SDDF}/tools/make/multikernel.mk
endif

CFLAGS += \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group


all: $(IMAGE_FILE)

${IMAGES}: libsddf_util_debug.a

client.o: ${TOP}/client.c
	$(CC) -c $(CFLAGS) -MMD -MP $< -o client.o
client.elf: client.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

ifeq ($(MULTIKERNEL),1)
$(MULTIKERNEL_MANIFEST): $(METAPROGRAM) $(IMAGES) $(DTB)
else
$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
endif
ifneq ($(strip $(DTS)),)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE) $(METAPROGRAM_ARGS)
else
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --output . --sdf $(SYSTEM_FILE) $(METAPROGRAM_ARGS)
endif
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	touch $@

ifneq ($(MULTIKERNEL),1)
$(IMAGE_FILE) $(REPORT_FILE): $(SYSTEM_FILE) $(wildcard *.data)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)
endif

qemu: $(IMAGE_FILE)
	$(QEMU) $(QEMU_ARCH_ARGS) \
			-nographic \
			-d guest_errors $(QEMU_SMP_ARGS)

clean::
	rm -f client.o client.d
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}

-include client.d
