#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug
# This example is specifically for the Odroid-C4 and qemu_arm_virt platforms

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := aarch64-none-elf
endif

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	I2C_DRIVER_DIR := meson
	TIMER_DRIV_DIR := meson
	CPU := cortex-a55
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_arm_virt)
	I2C_DRIVER_DIR := virtio
	TIMER_DRIV_DIR := arm
	CPU := cortex-a53
else
$(error Unsupported MICROKIT_BOARD given)
endif

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SYSTEM_FILE := board/$(MICROKIT_BOARD)/i2c.system

CC := $(TOOLCHAIN)-gcc
LD := $(TOOLCHAIN)-ld
AS := $(TOOLCHAIN)-as
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit
QEMU := qemu-system-aarch64

SDDF := $(abspath ../../)
UTIL := $(SDDF)/util
LIBCO := $(SDDF)/libco

I2C := $(SDDF)/i2c
I2C_DRIVER := $(SDDF)/drivers/i2c/${I2C_DRIVER_DIR}
TIMER_DRIVER := $(SDDF)/drivers/clock/${TIMER_DRIV_DIR}

IMAGES := virt.elf driver.elf client.elf timer.elf
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

COMMONFILES=$(UTIL)/printf.c $(UTIL)/putchar_debug.c

CLIENT_OBJS := $(LIBCO)/libco.o pn532.o client.o $(COMMONFILES:.c=.o) sddf_timer_client.o
VIRT_OBJS := $(I2C)/components/virt.o $(COMMONFILES:.c=.o)
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

$(BUILD_DIR)/virt.elf: $(addprefix $(BUILD_DIR)/, $(VIRT_OBJS))
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

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

qemu: $(IMAGE_FILE)
	sudo $(QEMU) -machine virt,virtualization=on \
			-cpu cortex-a53 \
			-serial mon:stdio \
			-device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
			-m size=2G \
			-global virtio-mmio.force-legacy=false \
			-d guest_errors \
			-chardev socket,path=/home/kwinter/TS/LionsOS/examples/kitty/vi2c2.sock0,id=vi2c \
			-device vhost-user-i2c-device,chardev=vi2c,id=i2c \
			-object memory-backend-file,id=mem,size=2G,mem-path=/dev/shm/qemu.ram,share=on \
			-numa node,memdev=mem

.PHONY: all compile clean

%.o:
	$(CC) $(CFLAGS) -c $(@:.o=.c) -o $@

clean:
	rm -f *.o *.elf .depend*
	find . -name \*.o |xargs --no-run-if-empty rm

