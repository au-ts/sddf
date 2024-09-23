#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip ${MICROKIT_SDK}),)
$(error MICROKIT_SDK must be specified)
endif

export FB_IMG ?= fb_img.jpeg
export BLOB ?= 0 
export BUILD_DIR ?= build
export MICROKIT_SDK
export MICROKIT_BOARD ?= qemu_virt_aarch64
export MICROKIT_CONFIG ?= debug
export SDDF := $(abspath ../..)

override FB_IMG := $(abspath ${FB_IMG})
override BUILD_DIR := $(abspath ${BUILD_DIR})
override MICROKIT_SDK := $(abspath ${MICROKIT_SDK})

IMAGE_FILE:= ${BUILD_DIR}/loader.img
REPORT_FILE:= ${BUILD_DIR}/report.txt

all: ${IMAGE_FILE}

qemu ${IMAGE_FILE} ${REPORT_FILE} clean clobber: ${BUILD_DIR}/Makefile FORCE
	${MAKE} -C ${BUILD_DIR} MICROKIT_SDK=${MICROKIT_SDK} BUILD_DIR=${BUILD_DIR} FB_IMG=${FB_IMG} $(notdir $@)

${BUILD_DIR}/Makefile: gpu.mk
	mkdir -p ${BUILD_DIR}
	cp gpu.mk $@

FORCE:
