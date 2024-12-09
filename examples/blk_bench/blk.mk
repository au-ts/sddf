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


MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit
BLK_BENCHMARK := ${SDDF}/examples/blk_bench
BENCHMARK := $(SDDF)/benchmark_blk
SERIAL_COMPONENTS := $(SDDF)/serial/components
UART_DRIVER := $(SDDF)/drivers/serial/$(UART_DRIV_DIR)
SERIAL_CONFIG_INCLUDE := ${BLK_BENCHMARK}/include/serial_config
BENCHMARK_CONFIG_INCLUDE := ${BLK_BENCHMARK}/include/benchmark_config

CONFIGS_INCLUDE := ${BLK_BENCHMARK}

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SYSTEM_FILE  := ${BLK_BENCHMARK}/board/$(MICROKIT_BOARD)/blk.system
IMAGE_FILE   := loader.img
REPORT_FILE  := report.txt

IMAGES := client.elf blk_virt.elf benchmark_blk.elf \
		  uart_driver.elf serial_virt_tx.elf
ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	IMAGES += sdmmc_driver.elf
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_virt_aarch64)
	IMAGES += blk_driver.elf
else
	$(error Unsupported MICROKIT_BOARD given)
endif

CFLAGS := -mcpu=$(CPU) \
		  -mstrict-align \
		  -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -Wall -Wno-unused-function \
		  -DMICROKIT_CONFIG_${MICROKIT_CONFIG} \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -I$(CONFIGS_INCLUDE) \
		  -I$(SERIAL_CONFIG_INCLUDE) \
		  -I$(BENCHMARK_CONFIG_INCLUDE)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util.a --end-group

CHECK_FLAGS_BOARD_MD5:=.board_cflags-$(shell echo -- ${CFLAGS} ${BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//')

${CHECK_FLAGS_BOARD_MD5}:
	-rm -f .board_cflags-*
	touch $@

%.elf: %.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

BLK_DRIVER   := $(SDDF)/drivers/blk/${BLK_DRIVER_DIR}

BLK_COMPONENTS := $(SDDF)/blk/components

all: $(IMAGE_FILE)

include ${BENCHMARK}/benchmark.mk
include ${BLK_DRIVER}/${BLK_DRIVER_MK}

include ${SDDF}/util/util.mk
include ${BLK_COMPONENTS}/blk_components.mk
include ${UART_DRIVER}/uart_driver.mk
include ${SERIAL_COMPONENTS}/serial_components.mk

${IMAGES}: libsddf_util.a

client.o: ${BLK_BENCHMARK}/client.c ${BLK_BENCHMARK}/basic_data.h
	$(CC) -c $(CFLAGS) -I. $< -o client.o
client.elf: client.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu_disk:
	$(SDDF)/tools/mkvirtdisk mydisk 1 512 16777216

qemu: ${IMAGE_FILE} qemu_disk
	$(QEMU) -machine virt,virtualization=on \
			-cpu cortex-a53 \
			-serial mon:stdio \
			-device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
			-m size=2G \
			-nographic \
            -global virtio-mmio.force-legacy=false \
            -d guest_errors \
            -drive file=mydisk,if=none,format=raw,id=hd \
            -device virtio-blk-device,drive=hd

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
