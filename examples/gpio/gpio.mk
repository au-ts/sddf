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

SUPPORTED_BOARDS := odroidc4

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := clang
endif

include ${SDDF}/tools/make/board/common.mk


# Driver paths
UTIL := $(SDDF)/util
LIBCO := $(SDDF)/libco
GPIO_TOP := ${SDDF}/examples/gpio
METAPROGRAM := $(GPIO_TOP)/meta.py
TIMER_TOP := ${SDDF}/examples/timer
GPIO_DRIVER := $(SDDF)/drivers/gpio/${PLATFORM}
TIMER_DRIVER := $(SDDF)/drivers/timer/${TIMER_DRIV_DIR}
SDDF_CUSTOM_LIBC := 1

SDFGEN_OUT = ${GPIO_TOP}/board/$(MICROKIT_BOARD)
SYSTEM_FILE := ${SDFGEN_OUT}/gpio.system

# Images to build
IMAGES := gpio_driver.elf timer_driver.elf client.elf motor_control_a.elf motor_control_b.elf ultrasonic_sensor.elf telemetry.elf

# Compiler flags
CFLAGS += \
          -Wall -Wno-unused-function \
          -I$(BOARD_DIR)/include \
          -I$(SDDF)/include \
          -I$(SDDF)/include/microkit \
          -I$(LIBCO) \
          -I${GPIO_TOP}

LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

COMMONFILES := libsddf_util_debug.a

CLIENT_OBJS := client.o
MOTOR_CONTROL_A_OBJS := motor_control_a.o
MOTOR_CONTROL_B_OBJS := motor_control_b.o
ULTRASONIC_SENSOR_OBJS := ultrasonic_sensor.o
TELEMETRY_OBJS := telemetry.o

VPATH := ${GPIO_TOP}

all: $(IMAGE_FILE)

# Client build
client.o: ${GPIO_TOP}/client.c
	$(CC) -c $(CFLAGS) $< -o $@

client.elf: $(CLIENT_OBJS) libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# Motor control build
motor_control_a.o: ${GPIO_TOP}/motor_control.c
	$(CC) -c $(CFLAGS) $< -o $@

motor_control_a.elf: $(MOTOR_CONTROL_A_OBJS) libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

motor_control_b.o: ${GPIO_TOP}/motor_control.c
	$(CC) -c $(CFLAGS) $< -o $@

motor_control_b.elf: $(MOTOR_CONTROL_B_OBJS) libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# Ultrasonic sensor build
ultrasonic_sensor.o: ${GPIO_TOP}/ultrasonic_sensor.c
	$(CC) -c $(CFLAGS) $< -o $@

ultrasonic_sensor.elf: $(ULTRASONIC_SENSOR_OBJS) libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

telemetry.o: ${GPIO_TOP}/telemetry.c
	$(CC) -c $(CFLAGS) $< -o $@

telemetry.elf: $(TELEMETRY_OBJS) libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
ifneq ($(strip $(DTS)),)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output ${SDFGEN_OUT} --sdf gpio.system
else
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --output ${SDFGEN_OUT} --sdf gpio.system
endif
	$(OBJCOPY) --update-section .device_resources=${SDFGEN_OUT}/timer_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=${SDFGEN_OUT}/timer_client_client.data client.elf
	$(OBJCOPY) --update-section .timer_client_config=${SDFGEN_OUT}/timer_client_motor_control_a.data motor_control_a.elf
	$(OBJCOPY) --update-section .timer_client_config=${SDFGEN_OUT}/timer_client_motor_control_b.data motor_control_b.elf
	$(OBJCOPY) --update-section .timer_client_config=${SDFGEN_OUT}/timer_client_ultrasonic_sensor.data ultrasonic_sensor.elf
	touch $@

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