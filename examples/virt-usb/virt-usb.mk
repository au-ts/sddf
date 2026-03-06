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

IMAGE_FILE = loader.img
REPORT_FILE = report.txt
BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug
TOOLCHAIN ?= clang

SUPPORTED_BOARDS:= qemu_virt_aarch64


include ${SDDF}/tools/make/board/common.mk

TOP := ${SDDF}/examples/virt-usb
METAPROGRAM := $(TOP)/meta.py
UTIL := $(SDDF)/util
TIMER_DRIVER := $(SDDF)/drivers/timer/$(TIMER_DRIV_DIR)
SYSTEM_FILE := virt-usb.system
SDDF_CUSTOM_LIBC := 1

IMAGES := client.elf pcie.elf usb.elf timer_driver.elf
CFLAGS +=  -Wno-unused-function -Werror

LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

TINYUSB := ${TOP}/tinyusb

CFLAGS += \
	-I${TOP}/include \
	-I${SDDF}/include \
	-I${SDDF}/include/microkit \
	-I${TOP} \
	-I${TINYUSB}/src \
	-I${TINYUSB}/src/portable/ehci \
	-I$(TINYUSB)/src/class \
	-I$(TINYUSB)/test \
	-I$(SDDF)/include/sddf/util \
	-DCFG_TUH_ENABLED=1 \
	-DTUP_USBIP_EHCI=1 \
	-DCFG_TUSB_MCU=OPT_MCU_VIRTAARCH64 \
	-DCFG_TUSB_DEBUG=3 \
    -DPRIu32='"u"' \
    -DPRIX32='"x"'


${IMAGES}: libsddf_util_debug.a

include ${TIMER_DRIVER}/timer_driver.mk
include ${SDDF}/util/util.mk

client.elf: client.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

client.o: ${TOP}/client.c
	$(CC) $(CFLAGS) -c -o $@ $<

pcie.elf: pcie.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

pcie.o: ${TOP}/pcie.c
	$(CC) $(CFLAGS) -c -o $@ $<


# tinyUSB source

tusb_fifo.o: $(TINYUSB)/src/common/tusb_fifo.c
	$(CC) -c $(CFLAGS) $< -o $@

ehci.o: $(TINYUSB)/src/portable/ehci/ehci.c
	$(CC) -c $(CFLAGS) $< -o $@

hcd_ehci_virt.o: $(TINYUSB)/src/portable/qemu/virt_aarch64/hcd_ehci_virt.c
	$(CC) -c $(CFLAGS) $< -o $@

tusb.o: $(TINYUSB)/src/tusb.c
	$(CC) -c $(CFLAGS) $< -o $@

hub.o: $(TINYUSB)/src/host/hub.c
	$(CC) -c $(CFLAGS) $< -o $@

usbh.o: $(TINYUSB)/src/host/usbh.c
	$(CC) -c $(CFLAGS) $< -o $@

usb.o: ${TOP}/usb.c
	$(CC) -c $(CFLAGS) $< -o usb.o

cdc_host.o: $(TINYUSB)/src/class/cdc/cdc_host.c
	$(CC) -c $(CFLAGS) $< -o $@

hid_host.o: $(TINYUSB)/src/class/hid/hid_host.c
	$(CC) -c $(CFLAGS) $< -o $@

msc_host.o: $(TINYUSB)/src/class/msc/msc_host.c
	$(CC) -c $(CFLAGS) $< -o $@

board.o: $(TINYUSB)/hw/bsp/board.c
	$(CC) -c $(CFLAGS) $< -o $@

# usb elf 

usb.elf: usb.o tusb.o hub.o usbh.o cdc_host.o hid_host.o msc_host.o ehci.o tusb_fifo.o board.o hcd_ehci_virt.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@




$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
# 	cp client.elf client0.elf
# 	cp client.elf client1.elf
ifneq ($(strip $(DTS)),)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
else
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --output . --sdf $(SYSTEM_FILE)
endif
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_usb.data usb.elf
	touch $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	MICROKIT_SDK=${MICROKIT_SDK} $(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

# NOTE: highmem=off is REQUIRED for it to boot
# I have otherwise removed "secure=off" but it may
# be in the end required
# I believe the default behaviour (highmem=on) allows PCIE physical memory
# to be mapped in high memory, which is not correctly handled by the existing PCIE code
# and I am not going to be fixing it right at this moment
# highmem-off could all break the hci driver which is 32bit only

# $(QEMU)
# ~/Work/qemu/build/qemu-system-aarch64-unsigned
qemu: ${IMAGE_FILE}
	$(QEMU) -machine virt,virtualization=on,highmem=off \
	-drive if=none,id=stick,format=raw,file=test.img \
	-cpu cortex-a53 \
	-serial mon:stdio \
	-device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
	-m size=2G \
	-nographic \
 	-device usb-ehci,id=ehci \
	-device usb-kbd,id=kbd,bus=ehci.0,port=1 \
 	--trace events="trace.txt",file="trace.out" \

#	-device usb-tablet,bus=ehci.0 \
# 	-device usb-storage,bus=ehci.0,drive=stick,id=flash \
#	-device usb-kbd,id=kbd,bus=ehci.0 \
# 	--trace "memory_region_ops_*" \
# 	-usb \
#	-s -S

clean::
	${RM} -f *.elf
	find . -name '*.[od]' | xargs ${RM} -f

clobber:: clean
	${RM} -f ${IMAGE_FILE} ${REPORT_FILE}

