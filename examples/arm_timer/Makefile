ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

BUILD_DIR ?= build
# By default we make a debug build so that the client debug prints can be seen.
MICROKIT_CONFIG ?= debug

MICROKIT_BOARD := qemu_arm_virt
CPU := cortex-a53

CC := clang
LD := ld.lld
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SDDF_DIR := $(abspath ../..)
TIMER_DRIVER_DIR := $(SDDF_DIR)/drivers/clock/arm
UTIL_DIR := $(SDDF_DIR)/util

CFLAGS := -mcpu=$(CPU) \
		  -mstrict-align \
		  -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -Wall -Wno-unused-function -Werror \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF_DIR)/include \
		  -I$(UTIL_DIR)/include \
		  -target aarch64-none-elf
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := -lmicrokit -Tmicrokit.ld

IMAGE_FILE = $(BUILD_DIR)/loader.img
REPORT_FILE = $(BUILD_DIR)/report.txt

UTIL := util.o printf.o minheap.o

TIMER_DRIVER_OBJS := timer_driver.o $(UTIL)
CLIENT_OBJS := client.o sddf_timer_client.o $(UTIL)

IMAGES := timer.elf client.elf

all: $(BUILD_DIR) $(IMAGE_FILE)

QEMU := qemu-system-aarch64

qemu: all
	# @ivanv: check that the amount of RAM given to QEMU is at least the number of RAM that QEMU is setup with for seL4.
	# if ! command -v $(QEMU) &> /dev/null; then echo "Could not find dependency: qemu-system-aarch64"; exit 1; fi
	$(QEMU) -machine virt,virtualization=on,highmem=off,secure=off \
			-cpu cortex-a53 \
			-serial mon:stdio \
			-device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
			-m size=2G \
			-nographic

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

# Utils
$(BUILD_DIR)/%.o : $(UTIL_DIR)/%.c
	$(CC) -c $(CFLAGS) $< -o $@

# Actual client
$(BUILD_DIR)/client.o:
	$(CC) -c $(CFLAGS) client.c -o $(BUILD_DIR)/client.o

# Driver
$(BUILD_DIR)/timer_driver.o: $(TIMER_DRIVER_DIR)/timer.c
	$(CC) -c $(CFLAGS) $(TIMER_DRIVER_DIR)/timer.c -o $(BUILD_DIR)/timer_driver.o

# Timer API for client
$(BUILD_DIR)/sddf_timer_client.o:
	BUILD_DIR=$(abspath $(BUILD_DIR)) MICROKIT_INCLUDE=$(BOARD_DIR)/include TIMER_CHANNEL=1 make -C $(SDDF_DIR)/timer/client

# Driver PD
$(BUILD_DIR)/timer.elf: $(addprefix $(BUILD_DIR)/,$(TIMER_DRIVER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# Client PD
$(BUILD_DIR)/client.elf: $(addprefix $(BUILD_DIR)/,$(CLIENT_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) timer.system
	$(MICROKIT_TOOL) timer.system --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)
