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

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := aarch64-none-elf
endif

ifeq (${MICROKIT_BOARD},odroidc4)
	PLATFORM := meson
	CPU := cortex-a55
else
$(error Unsupported MICROKIT_BOARD)
endif

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)

CC := $(TOOLCHAIN)-gcc
LD := $(TOOLCHAIN)-ld
AS := $(TOOLCHAIN)-as
AR := $(TOOLCHAIN)-ar
RANLIB := $(TOOLCHAIN)-ranlib

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

UTIL := $(SDDF)/util
LIBCO := $(SDDF)/libco
TOP := ${SDDF}/examples/i2c
I2C := $(SDDF)/i2c
I2C_DRIVER := $(SDDF)/drivers/i2c/${PLATFORM}
TIMER_DRIVER := $(SDDF)/drivers/clock/${PLATFORM}

IMAGES := i2c_virt.elf i2c_driver.elf client.elf timer_driver.elf
CFLAGS := -mcpu=$(CPU) -mstrict-align -ffreestanding -g3 -O3 -Wall -Wno-unused-function -I${TOP}
LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib -L${LIBC}
LIBS := --start-group -lmicrokit -Tmicrokit.ld -lc libsddf_util_debug.a --end-group

IMAGE_FILE = loader.img
REPORT_FILE = report.txt
SYSTEM_FILE = ${TOP}/board/$(MICROKIT_BOARD)/i2c.system

CFLAGS += -I$(BOARD_DIR)/include \
	-I$(SDDF)/include \
	-I$(LIBCO) \
	-MD \
	-MP

COMMONFILES=libsddf_util_debug.a

CLIENT_OBJS :=  pn532.o client.o
DEPS := $(CLIENT_OBJS:.o=.d)

VPATH:=${TOP}
all: $(IMAGE_FILE)

client.elf: $(CLIENT_OBJS) libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

${IMAGES}: ${COMMONFILES}
.PHONY: all compile clean

clean::
	rm -f *.elf
	find . -name '*.[do]' |xargs --no-run-if-empty rm

clobber:: clean
	rm -f ${REPORT_FILE} ${IMAGE_FILE} *.a .*cflags*

include ${SDDF}/util/util.mk
include ${I2C}/components/i2c_virt.mk
include ${TIMER_DRIVER}/timer_driver.mk
include ${LIBCO}/libco.mk
include ${I2C_DRIVER}/i2c_driver.mk
-include $(DEPS)
