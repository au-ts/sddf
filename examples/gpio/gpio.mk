#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Combined GPIO + Timer build
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(SDDF)),)
$(error SDDF must be specified)
endif

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug
IMAGE_FILE := loader.img
REPORT_FILE := report.txt

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := aarch64-none-elf
endif

# Board-specific configuration
ifeq (${MICROKIT_BOARD},odroidc4)
	PLATFORM := meson
	CPU := cortex-a55
	TIMER_DRIV_DIR := meson
else
$(error Unsupported MICROKIT_BOARD)
endif

# Toolchain setup
CC := $(TOOLCHAIN)-gcc
LD := $(TOOLCHAIN)-ld
AS := $(TOOLCHAIN)-as
AR := $(TOOLCHAIN)-ar
RANLIB := $(TOOLCHAIN)-ranlib
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)

# Driver paths
UTIL := $(SDDF)/util
LIBCO := $(SDDF)/libco
GPIO_TOP := ${SDDF}/examples/gpio
TIMER_TOP := ${SDDF}/examples/timer
GPIO_DRIVER := $(SDDF)/drivers/gpio/${PLATFORM}
TIMER_DRIVER := $(SDDF)/drivers/timer/${TIMER_DRIV_DIR}

SYSTEM_FILE := ${GPIO_TOP}/board/$(MICROKIT_BOARD)/gpio.system

# Images to build
IMAGES := gpio_driver.elf timer_driver.elf client.elf motor_control_a.elf motor_control_b.elf

# Compiler flags
CFLAGS := -mcpu=$(CPU) -mstrict-align -ffreestanding -g3 -O3 \
          -Wall -Wno-unused-function \
          -DCONFIG_EXPORT_PCNT_USER=1 \
          -DCONFIG_EXPORT_PTMR_USER=1 \
          -I$(BOARD_DIR)/include \
          -I$(SDDF)/include \
          -I$(SDDF)/include/microkit \
          -I$(LIBCO) \
          -I${GPIO_TOP} \
          -MD -MP

LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

COMMONFILES := libsddf_util_debug.a

CLIENT_OBJS := client.o
MOTOR_CONTROL_A_OBJS := motor_control_a.o
MOTOR_CONTROL_B_OBJS := motor_control_b.o

-include client.d
-include motor_control_a.d
-include motor_control_b.d


VPATH := ${GPIO_TOP}

all: $(IMAGE_FILE)

# Client build
client.o: ${GPIO_TOP}/client.c
	$(CC) -c $(CFLAGS) $< -o $@

client.elf: $(CLIENT_OBJS) libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# Motor control build, specify what channel the GPIO pins are
motor_control_a.o: ${GPIO_TOP}/motor_control.c
	$(CC) -c $(CFLAGS) $< -o $@

motor_control_a.elf: $(MOTOR_CONTROL_A_OBJS) libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

motor_control_b.o: ${GPIO_TOP}/motor_control.c
	$(CC) -c $(CFLAGS) $< -o $@

motor_control_b.elf: $(MOTOR_CONTROL_B_OBJS) libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@


# Final image generation
$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

${IMAGES}: ${COMMONFILES}

.PHONY: all clean clobber

clean::
	rm -f *.elf *.o *.d

clobber:: clean
	rm -f ${REPORT_FILE} ${IMAGE_FILE} *.a

# Include driver build rules
include ${SDDF}/util/util.mk
include ${LIBCO}/libco.mk
include ${GPIO_DRIVER}/gpio_driver.mk
include ${TIMER_DRIVER}/timer_driver.mk