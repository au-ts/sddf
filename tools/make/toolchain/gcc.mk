#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
ifndef BOARD_DIR
$(error BOARD_DIR not defined)
endif

ARCH := $(shell sed -n 's/#define *CONFIG_SEL4_ARCH  *\([^ ]*\).*$$/\1/p'  $(BOARD_DIR)/include/kernel/gen_config.h)
ifeq ($(ARCH),aarch64)
	TRIPLE := aarch64-none-elf
else ifeq ($(ARCH),riscv64)
	TRIPLE := riscv64-unknown-elf
else
$(error Unsupported ARCH given)
endif

ifdef CPU
CFLAGS_ARCH += \
	-mcpu=$(CPU) \
	-mtune=$(CPU)
endif

CC := ${TRIPLE}-gcc
AS := ${TRIPLE}-as
LD := ${TRIPLE}-ld
RANLIB := ${TRIPLE}-ranlib
AR := ${TRIPLE}-ar
OBJCOPY := ${TRIPLE}-objcopy
OBJDUMP := ${TRIPLE}-objdump
SIZE := ${TRIPLE}-size

OPTIMISATION ?= -g -O2

CFLAGS += \
	-MD \
	-mstrict-align \
	-ffreestanding \
	${OPTIMISATION} \
	-Wall \
	${CFLAGS_ARCH} \
	-I ${BOARD_DIR}/include
