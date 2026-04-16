#
# Copyright 2026, UNSW
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
		    x86_64_generic

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := clang
endif

include ${SDDF}/tools/make/board/common.mk

TOP := ${SDDF}/examples/pci
METAPROGRAM := $(TOP)/meta.py
UTIL := $(SDDF)/util
ACPI_DRIVER := $(SDDF)/drivers/acpi/acpi.mk
ACPI_DRIVER := $(SDDF)/drivers/pci/pci.mk
SYSTEM_FILE := pci.system
SDDF_CUSTOM_LIBC := 1

IMAGES := acpi_driver.elf pci_driver.elf

CFLAGS += \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group


all: $(IMAGE_FILE)

include ${SDDF}/drivers/acpi/acpi_driver.mk
include ${SDDF}/drivers/pci/pci_driver.mk
include ${SDDF}/util/util.mk

${IMAGES}: libsddf_util_debug.a

client.o: ${TOP}/client.c
	$(CC) -c $(CFLAGS) $< -o client.o
client.elf: client.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

# $(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
# ifneq ($(strip $(DTS)),)
# 	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
# else
# 	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(X86_BOARD) --output . --sdf $(SYSTEM_FILE)
# endif
# 	touch $@

$(SYSTEM_FILE): $(TOP)/$(SYSTEM_FILE) $(IMAGES)
	cp $< $@

$(IMAGE_FILE) $(REPORT_FILE): $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu: $(IMAGE_FILE)
	$(QEMU) $(QEMU_ARCH_ARGS) \
			-nographic \
			-d guest_errors

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
