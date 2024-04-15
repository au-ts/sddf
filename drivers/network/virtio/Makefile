#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_INCLUDE)),)
$(error MICROKIT_INCLUDE must be specified)
endif

ifeq ($(strip $(ETHERNET_CONFIG_INCLUDE)),)
$(error ETHERNET_CONFIG_INCLUDE must be specified)
endif

BUILD_DIR ?= .

TOOLCHAIN := clang
CC := clang
TARGET := aarch64-none-elf
SDDF := ../../..

CFLAGS := \
	-target $(TARGET) \
	-mstrict-align \
	-ffreestanding \
	-Wno-unused-function \
	-I$(MICROKIT_INCLUDE) \
	-I$(ETHERNET_CONFIG_INCLUDE) \
	-I$(SDDF)/include

all: $(BUILD_DIR)/ethernet.o

$(BUILD_DIR)/ethernet.o: ethernet.c ethernet.h
	$(CC) -c $(CFLAGS) ethernet.c -o $(BUILD_DIR)/ethernet.o

.PHONY: clean
clean:
	rm $(BUILD_DIR)/ethernet.o
