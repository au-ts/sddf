#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
CC := clang
LD := ld.lld
RANLIB := llvm-ranlib
AR := llvm-ar
OBJCOPY := llvm-objcopy
OBJDUMP := llvm-objdump
SIZE := llvm-size

OPTIMISATION ?= -g3 -O3

ifndef BOARD_DIR
$(error BOARD_DIR not defined)
endif

ARCH := $(shell sed -n 's/.define *CONFIG_SEL4_ARCH  *\([^ ]*\).*$$/\1/p'  $(BOARD_DIR)/include/kernel/gen_config.h)

ifeq ($(ARCH),aarch64)
	TARGET := aarch64-none-elf
else ifeq ($(ARCH),riscv64)
	CFLAGS_ARCH := -march=rv64imafdc
	TARGET := riscv64-none-elf
else
$(error Unsupported ARCH given)
endif

CFLAGS_ARCH += -target $(TARGET)

ifdef CPU
CFLAGS_ARCH += \
	-mcpu=$(CPU) \
	-mtune=$(CPU)
endif

CFLAGS += \
	-MD \
	-mstrict-align \
	-ffreestanding \
	${CFLAGS_ARCH} \
	${OPTIMISATION} \
	-Wall \
	-I ${BOARD_DIR}/include
