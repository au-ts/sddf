ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif
override MICROKIT_SDK := $(abspath ${MICROKIT_SDK})

BUILD_DIR ?= build
# By default we make a debug build so that the client debug prints can be seen.
MICROKIT_CONFIG ?= debug
MICROKIT_BOARD ?= odroidc4
CPU ?= cortex-a55
SDDF := $(abspath ../..)
CC := clang
LD := ld.lld
export MICROKIT_TOOL ?= $(abspath $(MICROKIT_SDK)/bin/microkit)

export BOARD_DIR := $(abspath $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG))
export SDDF := $(abspath ../..)
export TOP:= $(abspath $(dir ${MAKEFILE_LIST}))
TARGETS:= all clobber clean

${TARGETS}: $(IMAGE_FILE) ${BUILD_DIR}/Makefile FORCE
	${MAKE} -C ${BUILD_DIR} MICROKIT_SDK=${MICROKIT_SDK} $(filter ${TARGETS},$@)

${BUILD_DIR}/Makefile: timer.mk
	mkdir -p ${BUILD_DIR}
	cp timer.mk ${BUILD_DIR}/Makefile

FORCE:
