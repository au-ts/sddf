#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif
override MICROKIT_SDK := $(abspath ${MICROKIT_SDK})

BUILD_DIR ?= build
override BUILD_DIR := $(abspath ${BUILD_DIR})
export BUILD_DIR
export MICROKIT_CONFIG ?= debug
export MICROKIT_BOARD ?= maaxboard

export SDDF := $(abspath ../../)

IMAGE_FILE := $(BUILD_DIR)/loader.img
REPORT_FILE := $(BUILD_DIR)/report.txt

all: clean ${IMAGE_FILE}

${IMAGE_FILE}: ${BUILD_DIR}/Makefile
	${MAKE} -C ${BUILD_DIR} MICROKIT_SDK=${MICROKIT_SDK} $(notdir $@)

${BUILD_DIR}/Makefile: thermal_control.mk
	mkdir -p ${BUILD_DIR}
	cp thermal_control.mk ${BUILD_DIR}/Makefile

clean:
	rm -rfd $(BUILD_DIR)

FORCE:
