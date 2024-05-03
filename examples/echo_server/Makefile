#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

BUILD_DIR ?= build
export MICROKIT_CONFIG ?= debug

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif


ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := aarch64-none-elf
	export TOOLCHAIN := aarch64-none-elf
	export LIBC := $(dir $(realpath $(shell aarch64-none-elf-gcc --print-file-name libc.a)))
endif

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	export DRIV_DIR := meson
	export CPU := cortex-a55
else ifeq ($(strip $(MICROKIT_BOARD)), imx8mm_evk)
	export DRIV_DIR := imx
	export CPU := cortex-a53
else ifeq ($(strip $(MICROKIT_BOARD)), maaxboard)
	export DRIV_DIR := imx
	export CPU := cortex-a53
else
$(error Unsupported MICROKIT_BOARD given)
endif

export BUILD_DIR:=$(abspath ${BUILD_DIR})
export MICROKIT_SDK:=$(abspath ${MICROKIT_SDK})

export CC := $(TOOLCHAIN)-gcc
export LD := $(TOOLCHAIN)-ld
export AS := $(TOOLCHAIN)-as
export MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit
export SDDF=$(abspath ../..)
export ECHO_INCLUDE:=$(abspath .)/include

IMAGE_FILE := $(BUILD_DIR)/loader.img
REPORT_FILE := $(BUILD_DIR)/report.txt

${IMAGE_FILE} ${REPORT_FILE} clean clobber: ${BUILD_DIR}/Makefile FORCE
	${MAKE}  -C ${BUILD_DIR}  -${MAKEFLAGS} $(notdir $@)

${BUILD_DIR}/Makefile: echo.mk
	mkdir -p ${BUILD_DIR}
	cp echo.mk $@

FORCE:
