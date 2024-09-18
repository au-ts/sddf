#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(SDDF)),)
$(error SDDF must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := aarch64-none-elf
endif

ifeq ($(strip $(TOOLCHAIN)), clang)
	CC := clang -target aarch64-none-elf
	LD := ld.lld
	AR := llvm-ar
	RANLIB := llvm-ranlib
else
	CC := $(TOOLCHAIN)-gcc
	LD := $(TOOLCHAIN)-ld
	AS := $(TOOLCHAIN)-as
	AR := $(TOOLCHAIN)-ar
	RANLIB := $(TOOLCHAIN)-ranlib
endif

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug

DRIVER_DIR := imx
CPU := cortex-a53

TOP := $(SDDF)/examples/mmc_hotplug
CONFIGS_INCLUDE := $(TOP)/include/configs

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)

IMAGES := game.elf plug_controller.elf \
		  mmc_driver.elf blk_virt.elf \
		  uart_driver.elf serial_virt_tx.elf serial_virt_rx.elf \
		  timer_driver.elf

CFLAGS := -mcpu=$(CPU) \
		  -mstrict-align \
		  -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -MD \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -I$(CONFIGS_INCLUDE)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

IMAGE_FILE   := loader.img
REPORT_FILE  := report.txt
SYSTEM_FILE  := $(TOP)/board/$(MICROKIT_BOARD)/mmc_hotplug.system

MMC_DRIVER   := $(SDDF)/drivers/blk/mmc/$(DRIVER_DIR)
TIMER_DRIVER := $(SDDF)/drivers/timer/$(DRIVER_DIR)
UART_DRIVER  := $(SDDF)/drivers/serial/$(DRIVER_DIR)

BLK_COMPONENTS    := $(SDDF)/blk/components
SERIAL_COMPONENTS := $(SDDF)/serial/components

all: $(IMAGE_FILE)

include $(MMC_DRIVER)/mmc_driver.mk
include $(TIMER_DRIVER)/timer_driver.mk
include $(UART_DRIVER)/uart_driver.mk

include $(SDDF)/util/util.mk
include $(BLK_COMPONENTS)/blk_components.mk
include $(SERIAL_COMPONENTS)/serial_components.mk

$(IMAGES): libsddf_util_debug.a

game.o: $(TOP)/game.c
	$(CC) -c $(CFLAGS) $< -o game.o
game.elf: game.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

plug_controller.o: $(TOP)/plug_controller.c
	$(CC) -c $(CFLAGS) $^ -o plug_controller.o
plug_controller.elf: plug_controller.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

clean::
	rm -f game.[od] plug_controller.[od]
clobber:: clean
	rm -f game.elf plug_controller.elf $(IMAGE_FILE) $(REPORT_FILE)
