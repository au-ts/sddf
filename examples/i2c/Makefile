#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

# @ivanv: Changes any of the params given e.g SEL4CP_CONFIG,
# doesn't actually cause a re-compile. We should fix this.
ifeq ($(strip $(BUILD_DIR)),)
$(error BUILD_DIR must be specified)
endif

ifeq ($(strip $(SEL4CP_SDK)),)
$(error SEL4CP_SDK must be specified)
endif

ifeq ($(strip $(SEL4CP_BOARD)),)
$(error SEL4CP_BOARD must be specified)
endif

ifeq ($(strip $(SEL4CP_CONFIG)),)
$(error SEL4CP_CONFIG must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := aarch64-none-elf
endif

CPU := cortex-a53

CC := $(TOOLCHAIN)-gcc
LD := $(TOOLCHAIN)-ld
AS := $(TOOLCHAIN)-as
SEL4CP_TOOL ?= $(SEL4CP_SDK)/bin/sel4cp

I2C=$(abspath ../../drivers/i2c/odroidc4/)
SDDF=$(abspath ../../)
BENCHMARK=$(SDDF)/benchmark
UTIL=$(SDDF)/util

BOARD_DIR := $(SEL4CP_SDK)/board/$(SEL4CP_BOARD)/$(SEL4CP_CONFIG)

IMAGES := i2c.elf i2c_driver.elf
CFLAGS := -mcpu=$(CPU) -mstrict-align -ffreestanding -g3 -O3 -Wall -Wno-unused-function -DNO_ASSERT
LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := -lsel4cp -Tsel4cp.ld -lc

IMAGE_FILE = $(BUILD_DIR)/loader.img
REPORT_FILE = $(BUILD_DIR)/report.txt

CFLAGS += -I$(BOARD_DIR)/include \
	-I$(I2C)/include	\
	-Iinclude/arch	\
	-I$(UTIL)/include \
	-MD \
	-MP

# SERVERFILES: Files implementing the server side of the i2c stack
SERVERFILES=$(I2C)/i2c.c
DRIVERFILES=$(I2C)/i2c-driver.c $(I2C)/i2c-odroid-c4.c
COMMONFILES=$(I2C)/i2c-transport.c $(I2C)/sw_shared_ringbuffer.c $(I2C)/printf.c

SERVER_OBJS := $(I2C)/i2c.o $(COMMONFILES:.c=.o)
DRIVER_OBJS := $(I2C)/i2c_driver.o $(I2C)/i2c-odroid-c4.o $(COMMONFILES:.c=.o)

OBJS := $(sort $(addprefix $(BUILD_DIR)/, $(SERVER_OBJS) $(DRIVER_OBJS)))
DEPS := $(OBJS:.o=.d)

all: $(IMAGE_FILE)
-include $(DEPS)

$(BUILD_DIR)/%.d $(BUILD_DIR)/%.o: %.c Makefile
	mkdir -p `dirname $(BUILD_DIR)/$*.o`
	$(CC) -c $(CFLAGS) $< -o $(BUILD_DIR)/$*.o

$(BUILD_DIR)/%.o: %.s Makefile
	$(AS) -g3 -mcpu=$(CPU) $< -o $@

$(BUILD_DIR)/i2c.elf: $(addprefix $(BUILD_DIR)/, $(SERVER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/i2c_driver.elf: $(addprefix $(BUILD_DIR)/, $(DRIVER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) i2c.system
	$(SEL4CP_TOOL) i2c.system --search-path $(BUILD_DIR) --board $(SEL4CP_BOARD) --config $(SEL4CP_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

.PHONY: all compile clean

%.o:
	$(CC) $(CFLAGS) -c $(@:.o=.c) -o $@

clean:
	rm -f *.o *.elf .depend*
	find . -name \*.o |xargs --no-run-if-empty rm

