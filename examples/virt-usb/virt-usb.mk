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
SYSTEM_FILE := virt-usb.system
SDDF_CUSTOM_LIBC := 1

IMAGES := client.elf pcie.elf
CFLAGS +=  -Wno-unused-function -Werror

LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

CFLAGS += \
	-I${TOP}/include \
	-I${SDDF}/include \
	-I${SDDF}/include/microkit

${IMAGES}: libsddf_util_debug.a

include ${SDDF}/util/util.mk

client.elf: client.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

client.o: ${TOP}/client.c
	$(CC) $(CFLAGS) -c -o $@ $<

pcie.elf: pcie.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

pcie.o: ${TOP}/pcie.c
	$(CC) $(CFLAGS) -c -o $@ $<



$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
# 	cp client.elf client0.elf
# 	cp client.elf client1.elf
ifneq ($(strip $(DTS)),)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
else
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --output . --sdf $(SYSTEM_FILE)
endif
# 	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
# 	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
# 	$(OBJCOPY) --update-section .serial_virt_rx_config=serial_virt_rx.data serial_virt_rx.elf
# 	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
# 	$(OBJCOPY) --update-section .serial_client_config=serial_client_client0.data client0.elf
# 	$(OBJCOPY) --update-section .serial_client_config=serial_client_client1.data client1.elf
	touch $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	MICROKIT_SDK=${MICROKIT_SDK} $(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

# NOTE: highmem=off is REQUIRED for it to boot
# I have otherwise removed "secure=off" but it may
# be in the end required
qemu: ${IMAGE_FILE}
	$(QEMU) -machine virt,virtualization=on,highmem=off \
	-cpu cortex-a53 \
	-serial mon:stdio \
	-device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
	-m size=2G \
	-nographic \
	-usb \
	-device usb-ehci,id=ehci

clean::
	${RM} -f *.elf
	find . -name '*.[od]' | xargs ${RM} -f

clobber:: clean
	${RM} -f ${IMAGE_FILE} ${REPORT_FILE}

