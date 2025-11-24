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

SUPPORTED_BOARDS:= cheshire \
		   hifive_p550 \
		   imx8mm_evk \
		   imx8mp_evk \
		   imx8mp_iotgate \
		   imx8mq_evk \
		   maaxboard \
		   odroidc2 \
		   odroidc4 \
		   qemu_virt_aarch64 \
		   qemu_virt_riscv64 \
		   rockpro64 \
		   rpi4b_1gb \
		   serengeti \
		   star64 \
		   zcu102

include ${SDDF}/tools/make/board/common.mk

TOP := ${SDDF}/examples/serial
METAPROGRAM := $(TOP)/meta.py
UTIL := $(SDDF)/util
SERIAL_COMPONENTS := $(SDDF)/serial/components
UART_DRIVER := $(SDDF)/drivers/serial/$(UART_DRIV_DIR)
SYSTEM_FILE := serial.system
SDDF_CUSTOM_LIBC := 1

IMAGES := serial_driver.elf \
	  serial_virt_tx.elf serial_virt_rx.elf \
	  client.elf
CFLAGS +=  -Wno-unused-function -Werror

LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

CFLAGS += \
	-I${TOP}/include \
	-I${SDDF}/include \
	-I${SDDF}/include/microkit

${IMAGES}: libsddf_util_debug.a

include ${SDDF}/util/util.mk
include ${UART_DRIVER}/serial_driver.mk
include ${SERIAL_COMPONENTS}/serial_components.mk

client.elf: client.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

client.o: ${TOP}/client.c
	$(CC) $(CFLAGS) -c -o $@ $<

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_rx_config=serial_virt_rx.data serial_virt_rx.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client0.data client0.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client1.data client1.elf
	touch $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	MICROKIT_SDK=${MICROKIT_SDK} $(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu: ${IMAGE_FILE}
	$(QEMU) -nographic -d guest_errors $(QEMU_ARCH_ARGS)

clean::
	${RM} -f *.elf
	find . -name '*.[od]' | xargs ${RM} -f

clobber:: clean
	${RM} -f ${IMAGE_FILE} ${REPORT_FILE}
