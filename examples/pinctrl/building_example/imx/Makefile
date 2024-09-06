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

ifeq ($(strip $(MICROKIT_BOARD)), maaxboard)
	export TIMER_DRIVER_DIR := imx
	export PINCTRL_DRIVER_DIR := imx
	export CPU := cortex-a53
	export SOC := imx8mq-evk
	export DTS_FILE := $(TOP)/dts/maaxboard.dts
	export PINMUX_DEVICE := iomuxc
else ifeq ($(strip $(MICROKIT_BOARD)), imx8mq_evk)
	export TIMER_DRIVER_DIR := imx
	export PINCTRL_DRIVER_DIR := imx
	export CPU := cortex-a53
	export SOC := imx8mq-evk
	export DTS_FILE := $(TOP)/dts/imx8mq_evk.dts
	export PINMUX_DEVICE := iomuxc
else ifeq ($(strip $(MICROKIT_BOARD)), imx8mm_evk)
	export TIMER_DRIVER_DIR := imx
	export PINCTRL_DRIVER_DIR := imx
	export CPU := cortex-a53
	export SOC := imx8mm-evk
	export DTS_FILE := $(TOP)/dts/imx8mm_evk.dts
	export PINMUX_DEVICE := pinctrl
else
$(error Unsupported MICROKIT_BOARD given)
endif

CC := clang
LD := ld.lld
export MICROKIT_TOOL ?= $(abspath $(MICROKIT_SDK)/bin/microkit)

export BOARD_DIR := $(abspath $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG))
export SDDF := $(abspath ../../../..)
IMAGE_FILE := $(BUILD_DIR)/loader.img
REPORT_FILE := $(BUILD_DIR)/report.txt

all: clean ${IMAGE_FILE}

${IMAGE_FILE}: ${BUILD_DIR}/Makefile
	${MAKE} -C ${BUILD_DIR} MICROKIT_SDK=${MICROKIT_SDK} $(notdir $@)

${BUILD_DIR}/Makefile: pinctrl.mk
	mkdir -p ${BUILD_DIR}
	cp pinctrl.mk ${BUILD_DIR}/Makefile

clean:
	rm -rfd $(BUILD_DIR)

FORCE: