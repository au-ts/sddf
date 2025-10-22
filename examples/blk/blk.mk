#
# Copyright 2024, UNSW
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

# Allow to user to specify a custom partition
PARTITION :=
ifdef PARTITION
	PARTITION_ARG := --partition $(PARTITION)
endif

IMAGE_FILE := loader.img
REPORT_FILE  := report.txt
SYSTEM_FILE := blk.system

SUPPORTED_BOARDS := qemu_virt_aarch64 \
		    qemu_virt_riscv64 \
		    maaxboard \

TOP := ${SDDF}/examples/blk
CONFIGS_INCLUDE := ${TOP}
SDDF_CUSTOM_LIBC := 1

include ${SDDF}/tools/make/board/common.mk


IMAGES := blk_driver.elf client.elf blk_virt.elf serial_virt_tx.elf serial_driver.elf
CFLAGS +=  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit \
		  -I$(CONFIGS_INCLUDE)

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

METAPROGRAM := $(TOP)/meta.py

BLK_DRIVER := $(SDDF)/drivers/blk/${BLK_DRIV_DIR}
SERIAL_DRIVER := $(SDDF)/drivers/serial/${UART_DRIV_DIR}

all: $(IMAGE_FILE)

include ${SDDF}/drivers/blk/${BLK_DRIV_DIR}/blk_driver.mk
include ${SDDF}/drivers/serial/${UART_DRIV_DIR}/serial_driver.mk

ifdef BLK_NEED_TIMER
include ${SDDF}/drivers/timer/${TIMER_DRIV_DIR}/timer_driver.mk
IMAGES += timer_driver.elf
export BLK_NEED_TIMER
endif

include ${SDDF}/util/util.mk
include ${SDDF}/blk/components/blk_components.mk
include ${SDDF}/serial/components/serial_components.mk

${IMAGES}: libsddf_util_debug.a

client.o: ${TOP}/client.c ${TOP}/basic_data.h
	$(CC) -c $(CFLAGS) -I. $< -o client.o
client.elf: client.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) \
	$(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) \
	--dtb $(DTB) --output . --sdf $(SYSTEM_FILE) $(PARTITION_ARG) \
	$${BLK_NEED_TIMER:+--need_timer}
ifdef BLK_NEED_TIMER
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_blk_driver.data blk_driver.elf
endif
	$(OBJCOPY) --update-section .device_resources=blk_driver_device_resources.data blk_driver.elf
	$(OBJCOPY) --update-section .blk_driver_config=blk_driver.data blk_driver.elf
	$(OBJCOPY) --update-section .blk_virt_config=blk_virt.data blk_virt.elf
	$(OBJCOPY) --update-section .blk_client_config=blk_client_client.data client.elf
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client.data client.elf
	touch $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu_disk:
	$(SDDF)/tools/mkvirtdisk disk 1 512 16777216 GPT

qemu: ${IMAGE_FILE} qemu_disk
	$(QEMU) $(QEMU_ARCH_ARGS) \
	    -nographic \
	    -d guest_errors \
	    -global virtio-mmio.force-legacy=false \
	    -drive file=disk,if=none,format=raw,id=hd \
	    -device virtio-blk-device,drive=hd

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
