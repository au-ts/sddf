#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_INCLUDE)),)
$(error MICROKIT_INCLUDE must be specified)
endif

BUILD_DIR ?= .

CC := clang
TARGET := aarch64-none-elf
SDDF := ../../

CFLAGS := \
	-target $(TARGET) \
	-mstrict-align \
	-ffreestanding \
	-I$(MICROKIT_INCLUDE) \
	-I$(SDDF)/include \
	-I$(SDDF)/util/include

all: $(BUILD_DIR)/sddf_serial_sharedringbuffer.o

$(BUILD_DIR)/sddf_serial_sharedringbuffer.o: shared_ringbuffer.c $(SDDF)/include/sddf/serial/shared_ringbuffer.h
	$(CC) -c $(CFLAGS) shared_ringbuffer.c -o $(BUILD_DIR)/sddf_serial_sharedringbuffer.o

.PHONY: clean
clean:
	rm $(BUILD_DIR)/sddf_serial_sharedringbuffer.o
