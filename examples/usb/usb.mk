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
		    rpi4b_1gb

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := clang
endif

include ${SDDF}/tools/make/board/common.mk

TOP := ${SDDF}/examples/usb
METAPROGRAM := $(TOP)/meta.py
UTIL := $(SDDF)/util
TIMER_DRIVER := $(SDDF)/drivers/timer/$(TIMER_DRIV_DIR)
SYSTEM_FILE := timer.system
SDDF_CUSTOM_LIBC := 1

IMAGES := timer_driver.elf usb.elf

TINYUSB := $(TOP)/tinyusb
TINYUSB_SRC := $(TOP)/tinyusb/src

CFLAGS += \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit \
		  -I$(TOP) -I$(TINYUSB_SRC) -I$(TINYUSB)/hw/mcu/broadcom/ \
		  -I$(TINYUSB_SRC)/portable/synopsys/dwc2 \
		  -I$(TINYUSB_SRC)/class \
		  -I$(TINYUSB)/test \
		  -DCFG_TUSB_MCU=OPT_MCU_BCM2711 \
		  -DBCM_VERSION=2711 \
		  -DMICROKIT \
		  -DCFG_TUSB_DEBUG_PRINTF=sddf_printf_ \
		  -DPRIu32='"u"' \
		  -DPRIX32='"x"'
# 		  -DCFG_TUSB_DEBUG=3
# Temporary fix for PRIu32 and PRIX32 because we don't have a full inttypes header

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

# TINYUSB_SRC_FILES := \
# 	tusb.c \
# 	host/hub.c \
# 	host/usbh.c \
# 	portable/synopsys/dwc2/dcd_dwc2.c \
# 	portable/synopsys/dwc2/dwc2_common.c \
# 	portable/synopsys/dwc2/hcd_dwc2.c

all: $(IMAGE_FILE)

include ${TIMER_DRIVER}/timer_driver.mk
include ${SDDF}/util/util.mk

${IMAGES}: libsddf_util_debug.a

tusb.o: $(TINYUSB_SRC)/tusb.c
	$(CC) -c $(CFLAGS) $< -o $@

tusb_fifo.o: $(TINYUSB_SRC)/common/tusb_fifo.c
	$(CC) -c $(CFLAGS) $< -o $@

board.o: $(TINYUSB)/hw/bsp/board.c
	$(CC) -c $(CFLAGS) $< -o $@

hub.o: $(TINYUSB_SRC)/host/hub.c
	$(CC) -c $(CFLAGS) $< -o $@

usbh.o: $(TINYUSB_SRC)/host/usbh.c
	$(CC) -c $(CFLAGS) $< -o $@

dwc2_common.o: $(TINYUSB_SRC)/portable/synopsys/dwc2/dwc2_common.c
	$(CC) -c $(CFLAGS) $< -o $@

hcd_dwc2.o: $(TINYUSB_SRC)/portable/synopsys/dwc2/hcd_dwc2.c
	$(CC) -c $(CFLAGS) $< -o $@

usb.o: ${TOP}/usb.c
	$(CC) -c $(CFLAGS) $< -o usb.o

cdc_host.o: $(TINYUSB_SRC)/class/cdc/cdc_host.c
	$(CC) -c $(CFLAGS) $< -o $@

hid_host.o: $(TINYUSB_SRC)/class/hid/hid_host.c
	$(CC) -c $(CFLAGS) $< -o $@

msc_host.o: $(TINYUSB_SRC)/class/msc/msc_host.c
	$(CC) -c $(CFLAGS) $< -o $@

usb.elf: usb.o \
		 tusb.o \
		 tusb_fifo.o \
		 board.o \
		 hub.o \
		 usbh.o \
		 dwc2_common.o \
		 hcd_dwc2.o \
		 cdc_host.o \
		 hid_host.o \
		 msc_host.o
		 $(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
ifneq ($(strip $(DTS)),)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
else
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --output . --sdf $(SYSTEM_FILE)
endif
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_usb.data usb.elf
	touch $@

$(IMAGE_FILE) $(REPORT_FILE): $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu: $(IMAGE_FILE)
	$(QEMU) $(QEMU_ARCH_ARGS) \
			-nographic \
			-d guest_errors

clean::
	rm -f usb.o
clobber:: clean
	rm -f usb.elf ${IMAGE_FILE} ${REPORT_FILE}
