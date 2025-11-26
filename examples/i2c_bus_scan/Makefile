#
# Copyright 2023, UNSW
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
export MICROKIT_BOARD ?= odroidc4

export I2C_BUS_NUM := 2
export SDDF := $(abspath ../../)

IMAGE_FILE := $(BUILD_DIR)/loader.img
REPORT_FILE := $(BUILD_DIR)/report.txt

all: ${IMAGE_FILE}

${IMAGE_FILE} ${REPORT_FILE} clean clobber: ${BUILD_DIR}/Makefile FORCE
	${MAKE}  -C ${BUILD_DIR} MICROKIT_SDK=${MICROKIT_SDK}  $(notdir $@)

${BUILD_DIR}/Makefile: i2cscan.mk
	mkdir -p ${BUILD_DIR}
	cp i2cscan.mk $@
FORCE:
