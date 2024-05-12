ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

BUILD_DIR ?= build
# By default we make a debug build so that the client debug prints can be seen.
MICROKIT_CONFIG ?= debug
MICROKIT_BOARD ?= odroidc4
CPU ?= cortex-a55

CC := clang
LD := ld.lld
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
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

IMAGE_FILE := loader.img
REPORT_FILE := report.txt
SYSTEM_FILE := ${TOP}/board/$(MICROKIT_BOARD)/timer.system
CLIENT_OBJS := client.o
TIMER_DRIVER := $(SDDF)/drivers/clock/meson


all: $(IMAGE_FILE)

include ${TIMER_DRIVER}/timer.mk
include ${SDDF}/util/util.mk

client.o: ${TOP}/client.c
	$(CC) -c $(CFLAGS) $^ -o client.o
client.elf: client.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

clean::
	rm -f client.o
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE}
