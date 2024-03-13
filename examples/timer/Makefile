ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

BUILD_DIR ?= build
# By default we make a debug build so that the client debug prints can be seen.
MICROKIT_CONFIG ?= debug

MICROKIT_BOARD := odroidc4
CPU := cortex-a55

CC := clang
LD := ld.lld
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SDDF := $(abspath ../..)
UTIL := $(SDDF)/util

IMAGES := timer.elf client.elf
CFLAGS := -mcpu=$(CPU) \
		  -mstrict-align \
		  -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -Wall -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include \
		  -target aarch64-none-elf
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := -lmicrokit -Tmicrokit.ld

IMAGE_FILE = $(BUILD_DIR)/loader.img
REPORT_FILE = $(BUILD_DIR)/report.txt

TIMER_DRIVER_OBJS := timer_driver.o putchar_debug.o printf.o
CLIENT_OBJS := client.o $(BUILD_DIR)/sddf_timer_client.o

TIMER_DRIVER := $(SDDF)/drivers/clock/meson

all: $(BUILD_DIR) $(IMAGE_FILE)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/client.o: client.c
	$(CC) -c $(CFLAGS) $^ -o $(BUILD_DIR)/client.o

$(BUILD_DIR)/putchar_debug.o: $(UTIL)/putchar_debug.c
	$(CC) -c $(CFLAGS) $^ -o $(BUILD_DIR)/putchar_debug.o

$(BUILD_DIR)/printf.o: $(UTIL)/printf.c
	$(CC) -c $(CFLAGS) $^ -o $(BUILD_DIR)/printf.o

$(BUILD_DIR)/timer_driver.o: $(TIMER_DRIVER)/timer.c
	$(CC) -c $(CFLAGS) $(TIMER_DRIVER)/timer.c -o $(BUILD_DIR)/timer_driver.o

$(BUILD_DIR)/sddf_timer_client.o:
	BUILD_DIR=$(abspath $(BUILD_DIR)) MICROKIT_INCLUDE=$(BOARD_DIR)/include make -C $(SDDF)/timer/client

$(BUILD_DIR)/timer.elf: $(addprefix $(BUILD_DIR)/, $(TIMER_DRIVER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/client.elf: $(BUILD_DIR)/client.o $(BUILD_DIR)/sddf_timer_client.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) timer.system
	$(MICROKIT_TOOL) timer.system --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)
