#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(MICROKIT_BOARD)),)
$(error MICROKIT_BOARD must be specified)
endif

QEMU := qemu-system-aarch64
CC := clang
LD := ld.lld

MICROKIT_TOOL := $(MICROKIT_SDK)/bin/microkit
MICROKIT_CONFIG ?= debug
BUILD_DIR ?= build

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	ARCH := aarch64
	DRIVER_DIR := meson
	CPU := cortex-a55
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_arm_virt)
	ARCH := aarch64
	DRIVER_DIR := arm
	CPU := cortex-a53
else ifeq ($(strip $(MICROKIT_BOARD)), maaxboard)
	ARCH := aarch64
	DRIVER_DIR := imx
	CPU := cortex-a53
else ifeq ($(strip $(MICROKIT_BOARD)), star64)
	ARCH := riscv64
	DRIVER_DIR := star64
else
$(error Unsupported MICROKIT_BOARD given)
endif

SDDF=$(abspath ../..)
UTIL=$(SDDF)/util
SERIAL_COMPONENTS=$(SDDF)/serial/components
UART_DRIVER=$(SDDF)/drivers/serial/$(DRIVER_DIR)
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SYSTEM_FILE := board/$(MICROKIT_BOARD)/serial.system

CFLAGS := -ffreestanding -g3 -O3 -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument

ifeq ($(ARCH),aarch64)
	CFLAGS += -mcpu=$(CPU) -mstrict-align -target aarch64-none-elf
else ifeq ($(ARCH),riscv64)
	CFLAGS += -march=rv64imac -target riscv64-none-elf -DPRINTF_DISABLE_SUPPORT_FLOAT
endif

IMAGES := uart.elf serial_server_1.elf serial_server_2.elf virt_tx.elf virt_rx.elf
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := -lmicrokit -Tmicrokit.ld

IMAGE_FILE = $(BUILD_DIR)/loader.img
REPORT_FILE = $(BUILD_DIR)/report.txt

CFLAGS += -I$(BOARD_DIR)/include \
	-Iinclude	\
	-I$(UART_DRIVER)/include \
	-I$(SDDF)/include \

UART_OBJS := uart.o printf.o putchar_debug.o
SERIAL_SERVER_OBJS1 := serial_server_1.o
SERIAL_SERVER_OBJS2 := serial_server_2.o
VIRT_TX_OBJS := virt_tx.o
VIRT_RX_OBJS := virt_rx.o

all: directories $(IMAGE_FILE)

$(BUILD_DIR)/%.o: $(SERIAL_COMPONENTS)/%.c Makefile
	$(CC) -c $(CFLAGS) -DSERIAL_NUM_CLIENTS=2 -DSERIAL_TRANSFER_WITH_COLOUR $< -o $@

$(BUILD_DIR)/%.o: $(SERIAL_QUEUE)/%.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

$(BUILD_DIR)/%.o: $(UART_DRIVER)/%.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

$(BUILD_DIR)/printf.o: $(UTIL)/printf.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

$(BUILD_DIR)/putchar_debug.o: $(UTIL)/putchar_debug.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

$(BUILD_DIR)/serial_server_1.o: serial_server.c Makefile
	$(CC) -c $(CFLAGS) -DSERIAL_SERVER_NUMBER=1 $< -o $@

$(BUILD_DIR)/serial_server_2.o: serial_server.c Makefile
	$(CC) -c $(CFLAGS) -DSERIAL_SERVER_NUMBER=2 $< -o $@

$(BUILD_DIR)/virt_tx.elf: $(addprefix $(BUILD_DIR)/, $(VIRT_TX_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/virt_rx.elf: $(addprefix $(BUILD_DIR)/, $(VIRT_RX_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/uart.elf: $(addprefix $(BUILD_DIR)/, $(UART_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/serial_server_1.elf: $(addprefix $(BUILD_DIR)/, $(SERIAL_SERVER_OBJS1))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/serial_server_2.elf: $(addprefix $(BUILD_DIR)/, $(SERIAL_SERVER_OBJS2))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

.PHONY: all depend compile clean

qemu: all
	$(QEMU) -machine virt,virtualization=on -cpu cortex-a53 -serial mon:stdio -device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 -m size=2G -nographic

directories:
	mkdir -p $(BUILD_DIR)

clean:
	rm -f *.o *.elf .depend*
	find . -name \*.o |xargs --no-run-if-empty rm
