ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

BUILD_DIR ?= build
# By default we make a debug build so that the client debug prints can be seen.
MICROKIT_CONFIG ?= debug

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	ARCH := aarch64
	TIMER_DRIVER_DIR := meson
	CPU := cortex-a55
	LD := ld.lld
	CC := clang
else ifeq ($(strip $(MICROKIT_BOARD)), star64)
	ARCH := riscv64
	TIMER_DRIVER_DIR := starfive
	LD := ld.lld
	CC := clang
else
$(error Unsupported MICROKIT_BOARD given)
endif

# CC := riscv64-unknown-elf-gcc

# LD := ld.lld
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SDDF := $(abspath ../..)
UTIL := $(SDDF)/util

IMAGES := timer.elf client.elf
CFLAGS := -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O0 \
		   -Wno-unused-function -Werror -Wno-unused-command-line-argument \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/include
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := -lmicrokit -Tmicrokit.ld

ifeq ($(ARCH),aarch64)
	CFLAGS += -mcpu=$(CPU) -mstrict-align -target aarch64-none-elf
else ifeq ($(ARCH),riscv64)
	CFLAGS += -march=rv64imac -target riscv64-none-elf -DPRINTF_DISABLE_SUPPORT_FLOAT
endif

IMAGE_FILE = $(BUILD_DIR)/loader.img
REPORT_FILE = $(BUILD_DIR)/report.txt
SYSTEM_FILE = board/$(MICROKIT_BOARD)/timer.system

TIMER_DRIVER_OBJS := timer_driver.o putchar_debug.o printf.o
CLIENT_OBJS := client.o

TIMER_DRIVER := $(SDDF)/drivers/clock/$(TIMER_DRIVER_DIR)

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

$(BUILD_DIR)/timer.elf: $(addprefix $(BUILD_DIR)/, $(TIMER_DRIVER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/client.elf: $(BUILD_DIR)/client.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)
