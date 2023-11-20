#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(BUILD_DIR)),)
$(error BUILD_DIR must be specified)
endif

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(MICROKIT_CONFIG)),)
$(error MICROKIT_CONFIG must be specified)
endif

TOOLCHAIN := aarch64-none-elf

CPU := cortex-a53

CC := $(TOOLCHAIN)-gcc
LD := $(TOOLCHAIN)-ld
AS := $(TOOLCHAIN)-as
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit
MICROKIT_BOARD=odroidc4

SDDF=$(abspath ../..)
RINGBUFFERDIR=$(SDDF)/serial/libserialsharedringbuffer
SERIAL_COMPONENTS=$(SDDF)/serial/components
UART_DRIVER=$(SDDF)/drivers/serial/meson
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
UTIL=$(SDDF)/util

IMAGES := uart.elf serial_server_1.elf serial_server_2.elf mux_tx.elf mux_rx.elf
CFLAGS := -mcpu=$(CPU) -mstrict-align -ffreestanding -g3 -O3 -Wall -Wno-unused-function -DNO_ASSERT -Werror
LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := -lmicrokit -Tmicrokit.ld -lc

IMAGE_FILE = $(BUILD_DIR)/loader.img
REPORT_FILE = $(BUILD_DIR)/report.txt

CFLAGS += -I$(BOARD_DIR)/include \
	-Iinclude	\
	-I$(RINGBUFFERDIR)/include \
	-I$(UART_DRIVER)/include \
	-I$(UTIL)/include \

UART_OBJS := uart.o shared_ringbuffer.o
SERIAL_SERVER_OBJS1 := serial_server_1.o shared_ringbuffer.o
SERIAL_SERVER_OBJS2 := serial_server_2.o shared_ringbuffer.o
MUX_TX_OBJS := mux_tx.o shared_ringbuffer.o
MUX_RX_OBJS := mux_rx.o shared_ringbuffer.o

all: directories $(IMAGE_FILE)

$(BUILD_DIR)/%.o: $(SERIAL_COMPONENTS)/%.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

$(BUILD_DIR)/%.o: $(RINGBUFFERDIR)/%.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

$(BUILD_DIR)/%.o: $(UART_DRIVER)/%.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

$(BUILD_DIR)/%.o: %.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

$(BUILD_DIR)/%.o: %.s Makefile
	$(AS) -g3 -mcpu=$(CPU) $< -o $@

$(BUILD_DIR)/mux_tx.elf: $(addprefix $(BUILD_DIR)/, $(MUX_TX_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/mux_rx.elf: $(addprefix $(BUILD_DIR)/, $(MUX_RX_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/uart.elf: $(addprefix $(BUILD_DIR)/, $(UART_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/serial_server_1.elf: $(addprefix $(BUILD_DIR)/, $(SERIAL_SERVER_OBJS1))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/serial_server_2.elf: $(addprefix $(BUILD_DIR)/, $(SERIAL_SERVER_OBJS2))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) serial.system
	$(MICROKIT_TOOL) serial.system --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

.PHONY: all depend compile clean

%.o:
	$(CC) $(CFLAGS) -c $(@:.o=.c) -o $@

#Make the Directories
directories:
	$(info $(shell mkdir -p $(BUILD_DIR)/libsharedringbuffer))	\

clean:
	rm -f *.o *.elf .depend*
	find . -name \*.o |xargs --no-run-if-empty rm
