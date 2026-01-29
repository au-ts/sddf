#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile is copied into the build directory
# and operated on from there.
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := clang
endif

PYTHONPATH := ${SDDF}/tools/meta:${PYTHONPATH}
export PYTHONPATH

SUPPORTED_BOARDS := \
		maaxboard \
		odroidc4

include ${SDDF}/tools/make/board/common.mk

SDDF_CUSTOM_LIBC := 1
TOP:= ${SDDF}/examples/gpio
METAPROGRAM := $(TOP)/meta.py
UTIL := $(SDDF)/util
LIBCO := $(SDDF)/libco
GPIO_DRIVER := $(SDDF)/drivers/gpio/$(GPIO_DRIV_DIR)
TIMER_DRIVER := $(SDDF)/drivers/timer/${TIMER_DRIV_DIR}
SYSTEM_FILE := gpio.system
DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
CONFIGS_DIR   := $(TOP)/include
CONFIG_HEADER := $(CONFIGS_DIR)/gpio_config.h

IMAGES := gpio_driver.elf client.elf timer_driver.elf


IMAGE_FILE = loader.img
REPORT_FILE = report.txt
SYSTEM_FILE = gpio.system

CFLAGS += -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit \
		  -I$(LIBCO) \
		  -I$(CONFIGS_DIR) \
		  $(CFLAGS_ARCH)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group
all: $(IMAGE_FILE)

include ${GPIO_DRIVER}/gpio_driver.mk
include ${SDDF}/util/util.mk
include ${LIBCO}/libco.mk

${IMAGES}: libsddf_util_debug.a

# @Tristan: so it recompiles when the config file changes
-include client.d

client.o: ${TOP}/client.c $(CONFIG_HEADER)
	$(CC) -c $(CFLAGS) $< -o client.o
client.elf: client.o libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o client.elf

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=gpio_driver_device_resources.data gpio_driver.elf
	$(OBJCOPY) --update-section .gpio_client_config=gpio_client_client.data client.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client.data client.elf

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

${IMAGES}: libsddf_util_debug.a
.PHONY: all compile clean

clean::
	rm -f client.o
	find . -name '*.[do]' |xargs --no-run-if-empty rm

clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}

include ${TIMER_DRIVER}/timer_driver.mk
