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

DTC := dtc
PYTHON ?= python3

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit
BLK_BENCHMARK := ${SDDF}/examples/blk_bench
BENCHMARK := $(SDDF)/benchmark_blk
SERIAL_COMPONENTS := $(SDDF)/serial/components
UART_DRIVER := $(SDDF)/drivers/serial/$(UART_DRIV_DIR)
TIMER_DRIVER := $(SDDF)/drivers/timer/$(TIMER_DRIV_DIR)
SERIAL_CONFIG_INCLUDE := ${BLK_BENCHMARK}/include/serial_config
BENCHMARK_CONFIG_INCLUDE := ${BLK_BENCHMARK}/include/benchmark_config

CONFIGS_INCLUDE := ${BLK_BENCHMARK}

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
IMAGE_FILE   := loader.img
REPORT_FILE  := report.txt
SYSTEM_FILE  := blk.system

IMAGES := client.elf blk_virt.elf benchmark_blk.elf idle.elf \
		  serial_driver.elf serial_virt_tx.elf timer_driver.elf \
		  blk_driver.elf

CFLAGS := -mcpu=$(CPU) \
		  -mstrict-align \
		  -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -Wall -Wno-unused-function  -Werror -Wno-unused-command-line-argument \
		  -DMICROKIT_CONFIG_${MICROKIT_CONFIG} \
		  -DMICROKIT_BOARD_${MICROKIT_BOARD} \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -I$(CONFIGS_INCLUDE) \
		  -I$(SERIAL_CONFIG_INCLUDE) \
		  -I$(BENCHMARK_CONFIG_INCLUDE)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld
ifeq ($(strip $(MICROKIT_CONFIG)), debug)
	LIBS += libsddf_util_debug.a --end-group
else
	LIBS +=  libsddf_util.a  --end-group
endif

DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
METAPROGRAM := $(BLK_BENCHMARK)/meta.py

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
include ${BLK_DRIVER}/blk_driver.mk

include ${SDDF}/util/util.mk
include ${BLK_COMPONENTS}/blk_components.mk
include ${UART_DRIVER}/serial_driver.mk
include ${TIMER_DRIVER}/timer_driver.mk
include ${SERIAL_COMPONENTS}/serial_components.mk

ifeq ($(strip $(MICROKIT_CONFIG)), debug)
${IMAGES}: libsddf_util_debug.a
else
${IMAGES}: libsddf_util.a
endif

client.o: ${BLK_BENCHMARK}/client.c
	$(CC) -c $(CFLAGS) -I. $< -o client.o
ifeq ($(strip $(MICROKIT_CONFIG)), debug)
client.elf: client.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@
else
client.elf: client.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@
endif

$(DTB): $(DTS)
	dtc -q -I dts -O dtb $(DTS) > $(DTB)

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE) $(PARTITION_ARG)
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .device_resources=blk_driver_device_resources.data blk_driver.elf
	$(OBJCOPY) --update-section .blk_driver_config=blk_driver.data blk_driver.elf
	$(OBJCOPY) --update-section .blk_virt_config=blk_virt.data blk_virt.elf
	$(OBJCOPY) --update-section .blk_client_config=blk_client_client.data client.elf
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
ifdef BLK_DRIV_USE_TIMER
	$(OBJCOPY) --update-section .timer_client_config=timer_client_blk_driver.data blk_driver.elf
endif
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client.data client.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client.data client.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_bench.data benchmark_blk.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_bench.data benchmark_blk.elf
	$(OBJCOPY) --update-section .benchmark_blk_config=benchmark_blk_config.data benchmark_blk.elf
	$(OBJCOPY) --update-section .benchmark_blk_client_config=benchmark_blk_client_config.data client.elf
	$(OBJCOPY) --update-section .benchmark_config=benchmark_idle_config.data idle.elf

${IMAGE_FILE} $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
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
