#
# Copyright 2026, UNSW
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

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug

IMAGE_FILE := loader.img
REPORT_FILE  := report.txt
SYSTEM_FILE := usb.system

SUPPORTED_BOARDS := x86_64_generic

TOP := ${SDDF}/examples/usb
CONFIGS_INCLUDE := ${TOP}
SDDF_CUSTOM_LIBC := 1

include ${SDDF}/tools/make/board/common.mk


IMAGES := client.elf usb_hcd.elf

CFLAGS +=  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit \
		  -I$(CONFIGS_INCLUDE)

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

METAPROGRAM := $(TOP)/meta.py


# TODO: not hardcoded as xhci
USB_HCD_TYPE := xhci
USB_HCD := $(SDDF)/drivers/usb_hcd/${USB_HCD_TYPE}

all: $(IMAGE_FILE)

include ${USB_HCD}/usb_hcd.mk
include ${SDDF}/util/util.mk

${IMAGES}: libsddf_util_debug.a

client.o: ${TOP}/client.c
	$(CC) -c $(CFLAGS) -I. $< -o client.o

client.elf: client.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
ifneq ($(strip $(DTS)),)
	$(PYTHON) \
		$(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) \
		--dtb $(DTB) --output . --sdf $(SYSTEM_FILE) $(PARTITION_ARG) \
		$${BLK_NEED_TIMER:+--need_timer} \
		$${NVME:+--nvme}
else
	$(PYTHON) \
		$(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) \
		--output . --sdf $(SYSTEM_FILE) $(PARTITION_ARG) \
		$${BLK_NEED_TIMER:+--need_timer} \
		$${NVME:+--nvme}
endif

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu: ${IMAGE_FILE}
	$(QEMU) $(QEMU_ARCH_ARGS) $(QEMU_USB_HCD_ARGS) \
	    -nographic \
	    -d guest_errors

clean::
	rm -f client.o

clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}