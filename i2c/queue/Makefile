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
    -I$(SDDF)/include

all: $(BUILD_DIR)/sddf_i2c_queue.o

$(BUILD_DIR)/sddf_i2c_queue.o: queue.c $(SDDF)/include/sddf/i2c/queue.h
	$(CC) -c $(CFLAGS) queue.c -o $(BUILD_DIR)/sddf_i2c_queue.o

.PHONY: clean
clean:
	rm $(BUILD_DIR)/sddf_i2c_queue.o
