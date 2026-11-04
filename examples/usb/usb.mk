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
USB_DRIVER := $(SDDF)/drivers/usb/$(USB_DRIV_DIR)
SYSTEM_FILE := usb.system
SDDF_CUSTOM_LIBC := 1

IMAGES := timer_driver.elf usb_protocol.elf usb_driver.elf virt_hid.elf virt_msc.elf client.elf

TINYUSB := ${SDDF}/usb/tusb
TINYUSB_SRC := $(TINYUSB)/src
	
CFLAGS += \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -DCFG_TUSB_CONFIG_FILE="<tusb_config.h>" \
		  -DCFG_TUSB_MCU=OPT_MCU_BCM2711 \
		  -DBCM_VERSION=2711 \
 		  -DCFG_TUSB_DEBUG=0 \
		  -I$(TOP) \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit \
		  -I$(SDDF)/usb \
		  -I$(TINYUSB)/hw \
		  -I$(TINYUSB)/hw/mcu/broadcom \
		  -I$(TINYUSB_SRC) \
		  -I$(TINYUSB_SRC)/common \
		  -I$(TINYUSB_SRC)/portable/synopsys/dwc2

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

all: patched $(IMAGE_FILE)

include ${USB_DRIVER}/usb_driver.mk
include ${TIMER_DRIVER}/timer_driver.mk
include ${SDDF}/util/util.mk

${IMAGES}: libsddf_util_debug.a

patched:
	pushd $(SDDF)/usb; quilt push -a; popd; date > patched

usb_driver.elf: usb.o \
	tusb_fifo.o dwc2_common.o hcd_dwc2.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

usb_protocol.elf: protocol.o \
	board.o vcmailbox.o hcd_adapter.o dwc2_common.o \
	tusb.o tusb_fifo.o hub.o usbh.o hid_host.o msc_host.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

tusb.o: $(TINYUSB_SRC)/tusb.c
	$(CC) -c $(CFLAGS) $< -o $@

tusb_fifo.o: $(TINYUSB_SRC)/common/tusb_fifo.c
	$(CC) -c $(CFLAGS) $< -o $@

hub.o: $(TINYUSB_SRC)/host/hub.c
	$(CC) -c $(CFLAGS) $< -o $@

usbh.o: $(TINYUSB_SRC)/host/usbh.c
	$(CC) -c $(CFLAGS) $< -o $@

dwc2_common.o: $(TINYUSB_SRC)/portable/synopsys/dwc2/dwc2_common.c
	$(CC) -c $(CFLAGS) $< -o $@

hcd_dwc2.o: $(TINYUSB_SRC)/portable/synopsys/dwc2/hcd_dwc2.c
	$(CC) -c $(CFLAGS) $< -o $@

hcd_adapter.o: $(SDDF)/usb/components/hcd_adapter.c
	$(CC) -c $(CFLAGS) $< -o $@

protocol.o: $(SDDF)/usb/components/protocol.c
	$(CC) -c $(CFLAGS) $< -o $@

hid_host.o: $(TINYUSB_SRC)/class/hid/hid_host.c
	$(CC) -c $(CFLAGS) $< -o $@

msc_host.o: $(TINYUSB_SRC)/class/msc/msc_host.c
	$(CC) -c $(CFLAGS) $< -o $@

board.o: $(USB_DRIVER)/board.c
	$(CC) -c $(CFLAGS) $< -o $@

usb.o: $(USB_DRIVER)/usb.c
	$(CC) -c $(CFLAGS) $< -o $@

vcmailbox.o: $(TINYUSB)/hw/mcu/broadcom/broadcom/vcmailbox.c
	$(CC) -c $(CFLAGS) $< -o $@

controller.o: $(SDDF)/usb/components/controller.c
	$(CC) -c $(CFLAGS) $< -o $@

virt_msc.elf: virt_msc.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

virt_msc.o: $(SDDF)/usb/components/virt_msc.c
	$(CC) -c $(CFLAGS) $< -o $@

virt_hid.elf: virt_hid.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

virt_hid.o: $(SDDF)/usb/components/virt_hid.c
	$(CC) -c $(CFLAGS) $< -o $@

client.elf: client.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

client.o: $(SDDF)/examples/usb/client.c
	$(CC) -c $(CFLAGS) $< -o $@

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
ifneq ($(strip $(DTS)),)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
else
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --output . --sdf $(SYSTEM_FILE)
endif
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_usb_protocol.data usb_protocol.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_virt_hid.data virt_hid.elf
	touch $@

$(IMAGE_FILE) $(REPORT_FILE): patched $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

clean::
	${RM} -f *.elf
	find . -name '*.[od]' | xargs ${RM} -f
	cd $(SDDF)/usb && quilt pop -a && ${RM} -rf .pc

clobber:: clean
	${RM} -f ${IMAGE_FILE} ${REPORT_FILE}
