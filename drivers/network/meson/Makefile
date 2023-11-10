#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

MICROKIT_CONFIG ?= debug
MICROKIT_BOARD := odroidc4
CPU := cortex-a55

TOOLCHAIN := clang
CC := clang
LD := ld.lld
TARGET := aarch64-none-elf
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

LIBSHAREDRINGBUFFER=../../../network/libethsharedringbuffer

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)

CFLAGS := \
	-mtune=$(CPU) \
	-mstrict-align \
	-ffreestanding \
	-g \
	-O0 \
	-Wall \
	-Wno-unused-function \
	-I$(BOARD_DIR)/include \
	-I$(LIBSHAREDRINGBUFFER)/include \
	-target $(TARGET) \
	-DBOARD_$(MICROKIT_BOARD)
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := -lmicrokit -Tmicrokit.ld

all: ethernet.o

ethernet.o: ethernet.c ethernet.h
	$(CC) -c $(CFLAGS) ethernet.c -o ethernet.o

.PHONY: clean
clean:
	rm ethernet.o
