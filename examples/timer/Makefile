#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(MICROKIT_BOARD)),)
$(error MICROKIT_BOARD must be specified)
endif
export MICROKIT_BOARD
BUILD_DIR ?= build
export SDDF := $(abspath ../..)
export BUILD_DIR := $(abspath ${BUILD_DIR})
override MICROKIT_SDK := $(abspath ${MICROKIT_SDK})

IMAGE_FILE := $(BUILD_DIR)/loader.img
REPORT_FILE := $(BUILD_DIR)/report.txt

all: ${IMAGE_FILE}

qemu ${IMAGE_FILE} ${REPORT_FILE} clean clobber: $(IMAGE_FILE) ${BUILD_DIR}/Makefile FORCE
	${MAKE} -C ${BUILD_DIR} MICROKIT_SDK=${MICROKIT_SDK} $(notdir $@)

${BUILD_DIR}/Makefile: timer.mk
	mkdir -p ${BUILD_DIR}
	cp timer.mk ${BUILD_DIR}/Makefile

FORCE:
