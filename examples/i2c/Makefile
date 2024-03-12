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

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)

CC := $(TOOLCHAIN)-gcc
LD := $(TOOLCHAIN)-ld
AS := $(TOOLCHAIN)-as
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

SDDF := $(abspath ../../)
UTIL := $(SDDF)/util
LIBCO := $(SDDF)/libco

I2C := $(SDDF)/i2c
I2C_DRIVER := $(SDDF)/drivers/i2c/meson
I2C_QUEUE := $(I2C)/queue
TIMER_DRIVER := $(SDDF)/drivers/clock/meson

IMAGES := virtualiser.elf driver.elf client.elf timer.elf
CFLAGS := -mcpu=$(CPU) -mstrict-align -ffreestanding -g3 -O3 -Wall -Wno-unused-function
LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := -lmicrokit -Tmicrokit.ld -lc

IMAGE_FILE = $(BUILD_DIR)/loader.img
REPORT_FILE = $(BUILD_DIR)/report.txt

CFLAGS += -I$(BOARD_DIR)/include \
	-I$(SDDF)/include \
	-I$(LIBCO) \
	-MD \
	-MP

COMMONFILES=$(I2C_QUEUE)/queue.c $(UTIL)/printf.c $(UTIL)/putchar_debug.c

CLIENT_OBJS := $(LIBCO)/libco.o pn532.o client.o $(COMMONFILES:.c=.o) sddf_timer_client.o
VIRTUALISER_OBJS := $(I2C)/components/virtualiser.o $(COMMONFILES:.c=.o)
DRIVER_OBJS := $(I2C_DRIVER)/i2c.o $(COMMONFILES:.c=.o)
TIMER_DRIVER_OBJS := timer_driver.o $(UTIL)/printf.o $(UTIL)/putchar_debug.o

OBJS := $(sort $(addprefix $(BUILD_DIR)/, $(SERVER_OBJS) $(DRIVER_OBJS)))
DEPS := $(OBJS:.o=.d)

all: $(IMAGE_FILE)
-include $(DEPS)

$(BUILD_DIR)/%.d $(BUILD_DIR)/%.o: %.c Makefile
	mkdir -p `dirname $(BUILD_DIR)/$*.o`
	$(CC) -c $(CFLAGS) $< -o $(BUILD_DIR)/$*.o -DI2C_BUS_NUM=2

$(BUILD_DIR)/%.o: %.s Makefile
	$(AS) -g3 -mcpu=$(CPU) $< -o $@

$(BUILD_DIR)/virtualiser.elf: $(addprefix $(BUILD_DIR)/, $(VIRTUALISER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/driver.elf: $(addprefix $(BUILD_DIR)/, $(DRIVER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/client.elf: $(addprefix $(BUILD_DIR)/, $(CLIENT_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/sddf_timer_client.o:
	BUILD_DIR=$(abspath $(BUILD_DIR)) MICROKIT_INCLUDE=$(BOARD_DIR)/include make -C $(SDDF)/timer/client

$(BUILD_DIR)/timer.elf: $(addprefix $(BUILD_DIR)/, $(TIMER_DRIVER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/timer_driver.o: $(TIMER_DRIVER)/timer.c
	$(CC) -c $(CFLAGS) $(TIMER_DRIVER)/timer.c -o $(BUILD_DIR)/timer_driver.o

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) i2c.system
	$(MICROKIT_TOOL) i2c.system --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

.PHONY: all compile clean

%.o:
	$(CC) $(CFLAGS) -c $(@:.o=.c) -o $@

clean:
	rm -f *.o *.elf .depend*
	find . -name \*.o |xargs --no-run-if-empty rm

