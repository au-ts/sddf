#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

BUILD_DIR ?= build
# By default we make a debug build so that the client debug prints can be seen.
MICROKIT_CONFIG ?= debug

CC := aarch64-none-elf-gcc
LD := aarch64-none-elf-ld
AR := aarch64-none-elf-ar
AS := aarch64-none-elf-as
RANLIB := aarch64-none-elf-ranlib
PYTHON := python3

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
UTIL := $(SDDF)/util

IMAGES := timer_driver.elf pinctrl_driver.elf client.elf
CFLAGS := -mcpu=$(CPU) \
		  -mstrict-align \
		  -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -I$(LIBMICROKITCO_PATH) \
		  -I$(TOP)

LDFLAGS := -L$(BOARD_DIR)/lib -L.
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

IMAGE_FILE := loader.img
REPORT_FILE := report.txt
SYSTEM_FILE := ${TOP}/pinctrl.system
CLIENT_OBJS := client.o
PINCTRL_DRIVER := $(SDDF)/drivers/pinctrl/$(PINCTRL_DRIVER_DIR)
TIMER_DRIVER := $(SDDF)/drivers/timer/$(PINCTRL_DRIVER_DIR)

all: $(IMAGE_FILE)

${IMAGES}: libsddf_util_debug.a

include ${TIMER_DRIVER}/timer_driver.mk
include ${PINCTRL_DRIVER}/pinctrl_driver.mk
include ${SDDF}/util/util.mk

client.o: ${TOP}/client.c
	$(CC) -c $(CFLAGS) $(CHIP_HEADER_INC) -DSOC_$(shell echo $(SOC) | tr a-z A-Z | tr - _) $< -o client.o
client.elf: client.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(TOP)/build --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
