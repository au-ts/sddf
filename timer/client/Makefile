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
TARGET := x86_64-none-elf
SDDF := ../../

CFLAGS := \
	-target $(TARGET) \
	-mstrict-align \
	-ffreestanding \
	-I$(MICROKIT_INCLUDE) \
	-I$(SDDF)/include \
	-DTIMER_CHANNEL=$(TIMER_CHANNEL)

all: $(BUILD_DIR)/sddf_timer_client.o

$(BUILD_DIR)/sddf_timer_client.o: client.c $(SDDF)/include/sddf/timer/client.h
	$(CC) -c $(CFLAGS) client.c -o $(BUILD_DIR)/sddf_timer_client.o

.PHONY: clean
clean:
	rm $(BUILD_DIR)/sddf_timer_client.o
