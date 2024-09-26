#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif
override MICROKIT_SDK := $(abspath ${MICROKIT_SDK})

BUILD_DIR ?= build
# By default we make a debug build so that the client debug prints can be seen.
MICROKIT_CONFIG ?= debug

export TOP:= $(abspath $(dir ${MAKEFILE_LIST}))

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	export TIMER_DRIVER_DIR := meson
    export CLK_DRIVER_DIR := meson
	export CPU := cortex-a55
	export DTS_FILE := $(TOP)/odroidc4.dts
else
$(error Unsupported MICROKIT_BOARD given)
endif

CC := clang
LD := ld.lld
export MICROKIT_TOOL ?= $(abspath $(MICROKIT_SDK)/bin/microkit)

export BOARD_DIR := $(abspath $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG))
export SDDF := $(abspath ../..)
IMAGE_FILE := $(BUILD_DIR)/loader.img
REPORT_FILE := $(BUILD_DIR)/report.txt

all: clean ${IMAGE_FILE}

${IMAGE_FILE}: ${BUILD_DIR}/Makefile
	${MAKE} -C ${BUILD_DIR} MICROKIT_SDK=${MICROKIT_SDK} $(notdir $@)

${BUILD_DIR}/Makefile: clk.mk
	mkdir -p ${BUILD_DIR}
	cp clk.mk ${BUILD_DIR}/Makefile

clean:
	rm -rfd $(BUILD_DIR)

FORCE:
