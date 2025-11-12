#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

# Board-related common defines.
BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)

# Sanity checking:
# The board name must be supported for the project (i.e., in the
# SUPPORTED_BOARDS list); must have a corresponding board
# directory in the microkit SDK, and must have a makefile snippet
# in ${LIONSOS}/boards

ifeq ($(findstring $(strip ${MICROKIT_BOARD}),${SUPPORTED_BOARDS}),)
  $(error ${MICROKIT_BOARD} not (yet) supported for this project)
endif

ifeq ($(wildcard ${BOARD_DIR}),)
  $(error ${MICROKIT_BOARD} not supported by ${MICROKIT_SDK})
endif

ifeq ($(wildcard ${SDDF}/tools/make/board/${MICROKIT_BOARD}.mk),)
  $(error No Make snippet in ${SDDF}/tools/make/board for ${MICROKIT_BOARD})
endif

include ${SDDF}/tools/make/board/${MICROKIT_BOARD}.mk

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
DTC := dtc

PYTHON ?= python3

LDFLAGS := -L$(BOARD_DIR)/lib

# Common Make rules
%.elf: %.o
	${LD} ${LDFLAGS} -o $@ $< ${LIBS}

$(DTB): $(DTS)
	$(DTC) -q -I dts -O dtb $(DTS) > $(DTB)

# Some boards have more than one ethernet port.  The first is always called
# $(ETH_DRIV); projects that expect only one use eth_driver.elf
${ETH_DRIV}: libsddf_util_debug.a
eth_driver.elf: ${ETH_DRIV}
	cp ${ETH_DRIV} $@

include ${SDDF}/tools/make/toolchain/${TOOLCHAIN}.mk

# Magic to ensure stuff gets recompiled if we change
# board name, or use a different Microkit etc.
CHECK_FLAGS_BOARD_HASH := .board_cflags-$(shell echo -- ${CFLAGS} ${MICROKIT_SDK} ${MICROKIT_BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//g')

${CHECK_FLAGS_BOARD_HASH}:
	-rm -f .board_cflags-*
	touch $@

REBUILD_CANDIDATE_OBJECTS := $(shell find . -name '*.o')
${REBUILD_CANDIDATE_OBJECTS): .EXTRA_PREREQS = ${CHECK_FLAGS_BOARD_HASH}
