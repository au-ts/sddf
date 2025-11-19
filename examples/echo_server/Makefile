#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(MICROKIT_BOARD)),)
$(error MICROKIT_BOARD must be specified)
endif
BUILD_DIR ?= build
override BUILD_DIR := $(abspath ${BUILD_DIR})
export BUILD_DIR
export SDDF := $(abspath ../..)
override MICROKIT_SDK := $(abspath ${MICROKIT_SDK})
SMP_CONFIG ?=core_config/single_core.json
ifeq ($(wildcard ${SMP_CONFIG}),)
  $(error A valid SMP config .json file must be provided)
endif
override SMP_CONFIG:=$(abspath ${SMP_CONFIG})

IMAGE_FILE := $(BUILD_DIR)/loader.img
REPORT_FILE := $(BUILD_DIR)/report.txt

export ECHO_INCLUDE := $(abspath .)/include

all: ${IMAGE_FILE}

qemu ${IMAGE_FILE} ${REPORT_FILE} clean clobber: ${BUILD_DIR}/Makefile FORCE
	${MAKE}  -C ${BUILD_DIR} MICROKIT_SDK=${MICROKIT_SDK} SMP_CONFIG=${SMP_CONFIG} $(notdir $@)

${BUILD_DIR}/Makefile: echo.mk
	mkdir -p ${BUILD_DIR}
	cp echo.mk $@

FORCE:
