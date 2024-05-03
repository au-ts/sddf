#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := aarch64-none-elf
endif

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug
MICROKIT_BOARD ?= odroidc4
CPU ?= cortex-a55

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
export I2C_BUS_NUM:=2

CC := $(TOOLCHAIN)-gcc
LD := $(TOOLCHAIN)-ld
AS := $(TOOLCHAIN)-as
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

export SDDF := $(abspath ../../)

IMAGE_FILE := $(BUILD_DIR)/loader.img
REPORT_FILE := $(BUILD_DIR)/report.txt

all: ${IMAGE_FILE}

${IMAGE_FILE} ${REPORT_FILE} clean clobber: ${BUILD_DIR}/Makefile FORCE
	${MAKE}  -C ${BUILD_DIR}  -${MAKEFLAGS} $(notdir $@)

${BUILD_DIR}/Makefile: i2c.mk
	mkdir -p ${BUILD_DIR}
	cp i2c.mk $@
FORCE:
