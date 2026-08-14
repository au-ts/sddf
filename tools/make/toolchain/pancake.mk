#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
PANCAKE_COMPILER ?= cake

ifeq ($(ARCH),aarch64)
	PANCAKE_TARGET := arm8
else ifeq ($(ARCH),riscv64)
	PANCAKE_TARGET := riscv
else ifeq ($(ARCH),x86_64)
    PANCAKE_TARGET := x64
else
$(error Unsupported ARCH given)
endif

PANCAKE_FLAGS += \
	--pancake \
	--target=$(PANCAKE_TARGET) \
	--main_return=true
