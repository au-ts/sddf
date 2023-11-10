#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_INCLUDE)),)
$(error MICROKIT_INCLUDE must be specified)
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
	-I$(SDDF)/include

all: $(BUILD_DIR)/meson_ethernet.o

$(BUILD_DIR)/meson_ethernet.o: ethernet.c ethernet.h
	$(CC) -c $(CFLAGS) ethernet.c -o $(BUILD_DIR)/meson_ethernet.o

.PHONY: clean
clean:
	rm $(BUILD_DIR)/meson_ethernet.o
