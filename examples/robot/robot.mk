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

SUPPORTED_BOARDS := maaxboard

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := clang
endif

include ${SDDF}/tools/make/board/common.mk

# Driver paths
UTIL := $(SDDF)/util
LIBCO := $(SDDF)/libco
ROBOT_TOP := ${SDDF}/examples/robot
METAPROGRAM := $(ROBOT_TOP)/meta.py
TIMER_TOP := ${SDDF}/examples/timer
GPIO_DRIVER := $(SDDF)/drivers/gpio/${GPIO_DRIV_DIR}
TIMER_DRIVER := $(SDDF)/drivers/timer/${TIMER_DRIV_DIR}
SDDF_CUSTOM_LIBC := 1
CONFIGS_DIR   := $(ROBOT_TOP)/include/gpio_common
CONFIG_HEADER := $(CONFIGS_DIR)/gpio_config.h
PWM_DRIVER := $(SDDF)/drivers/pwm/${PWM_DRIV_DIR}
PINCTRL_DRIVER := $(SDDF)/drivers/pinctrl/${PINCTRL_DRIV_DIR}
CLK_DRIVER := $(SDDF)/drivers/clk/${CLK_DRIV_DIR}
SERIAL_DRIVER := $(SDDF)/drivers/serial/${UART_DRIV_DIR}


SDFGEN_OUT = ${ROBOT_TOP}/board/$(MICROKIT_BOARD)
SYSTEM_FILE := ${SDFGEN_OUT}/robot.system

# Images to build
IMAGES := pwm_driver.elf gpio_driver.elf timer_driver.elf client.elf telemetry.elf clk_driver.elf pinctrl_driver.elf  serial_virt_tx.elf serial_driver.elf 

# Compiler flags
CFLAGS += \
          -Wall -Wno-unused-function \
          -I$(BOARD_DIR)/include \
          -I$(SDDF)/include \
          -I$(SDDF)/include/microkit \
          -I$(LIBCO) \
          -I${ROBOT_TOP} \
		  -I$(CONFIGS_DIR)

# HACK for Pinctrl
ASFLAGS := -target aarch64-none-elf

LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

COMMONFILES := libsddf_util_debug.a

GPIO_COMMON_OBJS := gpio_common.o
CLIENT_OBJS := client.o
MOTOR_CONTROL_OBJS := motor_control.o
ULTRASONIC_SENSOR_OBJS := ultrasonic_sensor.o
TELEMETRY_OBJS := telemetry.o
TIMER_QUEUE_OBJS = timer_queue.o

VPATH := ${ROBOT_TOP}

all: $(IMAGE_FILE)

gpio_common.o: ${ROBOT_TOP}/gpio_common.c $(CONFIG_HEADER)
	$(CC) -c $(CFLAGS) $< -o $@

timer_queue.o: ${ROBOT_TOP}/timer_queue.c
	$(CC) -c $(CFLAGS) $< -o $@

# Motor control build
motor_control.o: ${ROBOT_TOP}/motor_control.c 
	$(CC) -c $(CFLAGS) $< -o $@

# Ultrasonic sensor build
ultrasonic_sensor.o: ${ROBOT_TOP}/ultrasonic_sensor.c
	$(CC) -c $(CFLAGS) $< -o $@

telemetry.o: ${ROBOT_TOP}/telemetry.c
	$(CC) -c $(CFLAGS) $< -o $@

telemetry.elf: $(TELEMETRY_OBJS) libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# Client build
client.o: ${ROBOT_TOP}/client.c 
	$(CC) -c $(CFLAGS) $< -o $@

client.elf: $(CLIENT_OBJS) ${ULTRASONIC_SENSOR_OBJS} ${TIMER_QUEUE_OBJS} ${GPIO_COMMON_OBJS} ${MOTOR_CONTROL_OBJS} libco.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
ifneq ($(strip $(DTS)),)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output ${SDFGEN_OUT} --sdf robot.system
else
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --output ${SDFGEN_OUT} --sdf robot.system
endif
	$(OBJCOPY) --update-section .device_resources=${SDFGEN_OUT}/timer_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .device_resources=${SDFGEN_OUT}/gpio_driver_device_resources.data gpio_driver.elf
	$(OBJCOPY) --update-section .gpio_client_config=${SDFGEN_OUT}/gpio_client_client.data client.elf
	$(OBJCOPY) --update-section .timer_client_config=${SDFGEN_OUT}/timer_client_client.data client.elf
	
	$(OBJCOPY) --update-section .device_resources=${SDFGEN_OUT}/serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .device_resources=${SDFGEN_OUT}/pinctrl_driver_device_resources.data pinctrl_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=${SDFGEN_OUT}/serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=${SDFGEN_OUT}/serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .serial_client_config=${SDFGEN_OUT}/serial_client_client.data client.elf

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
include ${CLK_DRIVER}/clk_driver.mk
include ${PWM_DRIVER}/pwm_driver.mk
include ${SERIAL_DRIVER}/serial_driver.mk
include ${PINCTRL_DRIVER}/pinctrl_driver.mk
include ${SDDF}/serial/components/serial_components.mk
