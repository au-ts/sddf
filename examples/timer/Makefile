ifeq ($(strip $(SEL4CP_SDK)),)
$(error SEL4CP_SDK must be specified)
endif

BUILD_DIR ?= build
# By default we make a debug build so that the client debug prints can be seen.
SEL4CP_CONFIG ?= debug

SEL4CP_BOARD := odroidc4
CPU := cortex-a53

CC := clang
LD := ld.lld
SEL4CP_TOOL ?= $(SEL4CP_SDK)/bin/sel4cp

BOARD_DIR := $(SEL4CP_SDK)/board/$(SEL4CP_BOARD)/$(SEL4CP_CONFIG)
SDDF := $(abspath ../..)

IMAGES := timer.elf client.elf
CFLAGS := -mcpu=$(CPU) \
		  -mstrict-align \
		  -nostdlib \
		  -ffreestanding \
		  -g3 \
		  -O3 \
		  -Wall -Wno-unused-function -Werror \
		  -I$(BOARD_DIR)/include \
		  -I$(SDDF)/drivers/clock/meson \
		  -target aarch64-none-elf
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := -lsel4cp -Tsel4cp.ld

IMAGE_FILE = $(BUILD_DIR)/loader.img
REPORT_FILE = $(BUILD_DIR)/report.txt

TIMER_OBJS := timer.o
CLIENT_OBJS := client.o

TIMER_DRIVER := $(SDDF)/drivers/clock/meson

all: $(BUILD_DIR) $(IMAGE_FILE)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/%.o: %.c
	$(CC) -c $(CFLAGS) $< -o $@

$(BUILD_DIR)/%.o: $(TIMER_DRIVER)/%.c
	$(CC) -c $(CFLAGS) $< -o $@

$(BUILD_DIR)/timer.elf: $(addprefix $(BUILD_DIR)/, $(TIMER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/client.elf: $(addprefix $(BUILD_DIR)/, $(CLIENT_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) timer.system
	$(SEL4CP_TOOL) timer.system --search-path $(BUILD_DIR) --board $(SEL4CP_BOARD) --config $(SEL4CP_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)
