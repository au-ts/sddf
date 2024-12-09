#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := aarch64-none-elf
	export TOOLCHAIN := aarch64-none-elf
	export LIBC := $(dir $(realpath $(shell aarch64-none-elf-gcc --print-file-name libc.a)))
endif

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	export MICROKIT_BOARD
	export UART_DRIV_DIR := meson
	export TIMER_DRIV_DIR := meson
	export BLK_DRIVER_DIR := sdmmc
	export CPU := cortex-a53
	export BLK_DRIVER_MK := sdmmc_driver.mk
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_virt_aarch64)
	export MICROKIT_BOARD
	export UART_DRIV_DIR := arm
	export TIMER_DRIV_DIR := arm
	export BLK_DRIVER_DIR := virtio
	export CPU := cortex-a53
	export QEMU := qemu-system-aarch64
	export BLK_DRIVER_MK := blk_driver.mk
else
	$(error Unsupported MICROKIT_BOARD given)
endif

BUILD_DIR ?= build
export MICROKIT_CONFIG ?= debug
export SDDF=$(abspath ../..)
export BUILD_DIR:=$(abspath ${BUILD_DIR})
export override MICROKIT_SDK:=$(abspath ${MICROKIT_SDK})
export CC := $(TOOLCHAIN)-gcc
export LD := $(TOOLCHAIN)-ld
export AS := $(TOOLCHAIN)-as
export AR := $(TOOLCHAIN)-ar
export RANLIB := $(TOOLCHAIN)-ranlib

IMAGE_FILE:= ${BUILD_DIR}/loader.img
REPORT_FILE:= ${BUILD_DIR}/report.txt

all: ${IMAGE_FILE}

qemu ${IMAGE_FILE} ${REPORT_FILE} clean clobber: ${BUILD_DIR}/Makefile FORCE
	${MAKE} -C ${BUILD_DIR}  MICROKIT_SDK=${MICROKIT_SDK} $(notdir $@)

${BUILD_DIR}/Makefile: blk.mk
	mkdir -p ${BUILD_DIR}
	cp blk.mk $@

FORCE:
