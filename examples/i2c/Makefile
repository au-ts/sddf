#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug
# This example is specifically for the Odroid-C4 platform
MICROKIT_BOARD := odroidc4

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := aarch64-none-elf
endif

MICROKIT_BOARD ?= odroidc4
CPU := cortex-a55

CC := $(TOOLCHAIN)-gcc
LD := $(TOOLCHAIN)-ld
AS := $(TOOLCHAIN)-as
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

I2C=$(abspath ../../drivers/i2c/odroidc4/)
SDDF=$(abspath ../../)
BENCHMARK=$(SDDF)/benchmark
UTIL=$(SDDF)/util
LIBCO := $(SDDF)/libco

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)

IMAGES := i2c.elf i2c_driver.elf client.elf
CFLAGS := -mcpu=$(CPU) -mstrict-align -ffreestanding -g3 -O3 -Wall -Wno-unused-function -DNO_ASSERT
LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := -lmicrokit -Tmicrokit.ld -lc

IMAGE_FILE = $(BUILD_DIR)/loader.img
REPORT_FILE = $(BUILD_DIR)/report.txt

CFLAGS += -I$(BOARD_DIR)/include \
	-I$(I2C)/include	\
	-Iinclude/arch	\
	-I$(UTIL)/include \
	-I$(LIBCO) \
	-MD \
	-MP

# SERVERFILES: Files implementing the server side of the i2c stack
CLIENT := client.c
SERVERFILES=$(I2C)/i2c.c
DRIVERFILES=$(I2C)/i2c-driver.c
COMMONFILES=$(I2C)/i2c-transport.c $(I2C)/sw_shared_ringbuffer.c $(I2C)/printf.c
# FOOLFILES=$(I2C)/fool.c $(I2C)/printf.c

CLIENT_OBJS := $(LIBCO)/libco.o helpers.o client.o $(COMMONFILES:.c=.o)
SERVER_OBJS := $(I2C)/i2c.o $(COMMONFILES:.c=.o)
DRIVER_OBJS := $(I2C)/i2c_driver.o $(COMMONFILES:.c=.o)
# FOOL_OBJS := $(I2C)/fool.o $(I2C)/printf.o

OBJS := $(sort $(addprefix $(BUILD_DIR)/, $(SERVER_OBJS) $(DRIVER_OBJS)))
DEPS := $(OBJS:.o=.d)

all: $(IMAGE_FILE)
-include $(DEPS)

$(BUILD_DIR)/%.d $(BUILD_DIR)/%.o: %.c Makefile
	mkdir -p `dirname $(BUILD_DIR)/$*.o`
	$(CC) -c $(CFLAGS) $< -o $(BUILD_DIR)/$*.o -DBUS_NUM=2

$(BUILD_DIR)/%.o: %.s Makefile
	$(AS) -g3 -mcpu=$(CPU) $< -o $@

$(BUILD_DIR)/i2c.elf: $(addprefix $(BUILD_DIR)/, $(SERVER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/i2c_driver.elf: $(addprefix $(BUILD_DIR)/, $(DRIVER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/client.elf: $(addprefix $(BUILD_DIR)/, $(CLIENT_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# $(BUILD_DIR)/fool.elf: $(addprefix $(BUILD_DIR)/, $(FOOL_OBJS))
# 	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) i2c.system
	$(MICROKIT_TOOL) i2c.system --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

.PHONY: all compile clean

%.o:
	$(CC) $(CFLAGS) -c $(@:.o=.c) -o $@

clean:
	rm -f *.o *.elf .depend*
	find . -name \*.o |xargs --no-run-if-empty rm

