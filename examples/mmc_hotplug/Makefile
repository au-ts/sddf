#
# Copyright 2024, UNSW
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

export MICROKIT_BOARD
export SDDF=$(abspath ../..)
export override MICROKIT_SDK:=$(abspath ${MICROKIT_SDK})
export BUILD_DIR:=$(abspath ${BUILD_DIR})

IMAGE_FILE:= ${BUILD_DIR}/loader.img
REPORT_FILE:= ${BUILD_DIR}/report.txt

all: ${IMAGE_FILE}

${IMAGE_FILE} ${REPORT_FILE} clean clobber: ${BUILD_DIR}/Makefile FORCE
	${MAKE} -C ${BUILD_DIR} $(notdir $@)

${BUILD_DIR}/Makefile: mmc_hotplug.mk
	mkdir -p ${BUILD_DIR}
	cp mmc_hotplug.mk $@

FORCE:
