#
# Copyright 2026, UNSW
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

IMAGE_FILE := loader.img
REPORT_FILE  := report.txt
SYSTEM_FILE := pwm.system

SUPPORTED_BOARDS := maaxboard

TOP := ${SDDF}/examples/pwm
CONFIGS_INCLUDE := ${TOP}
SDDF_CUSTOM_LIBC := 1

include ${SDDF}/tools/make/board/common.mk


IMAGES := pwm_driver.elf client.elf serial_virt_tx.elf serial_driver.elf clk_driver.elf
CFLAGS +=  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(SDDF)/include \
		  -I$(SDDF)/include/microkit \
		  -I$(CONFIGS_INCLUDE)

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

METAPROGRAM := $(TOP)/meta.py

PWM_DRIVER := $(SDDF)/drivers/pwm/${PWM_DRIV_DIR}
CLK_DRIVER := $(SDDF)/drivers/clk/${CLK_DRIV_DIR}
SERIAL_DRIVER := $(SDDF)/drivers/serial/${UART_DRIV_DIR}

all: $(IMAGE_FILE)

include ${CLK_DRIVER}/clk_driver.mk
include ${PWM_DRIVER}/pwm_driver.mk
include ${SERIAL_DRIVER}/serial_driver.mk

include ${SDDF}/util/util.mk
# include ${SDDF}/pwm/components/pwm_components.mk
include ${SDDF}/serial/components/serial_components.mk

${IMAGES}: libsddf_util_debug.a

client.o: ${TOP}/client.c
	$(CC) -c $(CFLAGS) -I. $< -o client.o

client.elf: client.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) \
		$(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) \
		--dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client.data client.elf
	touch $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
