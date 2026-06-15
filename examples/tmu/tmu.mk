#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile is copied into the build directory
# and operated on from there.
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := clang
endif

PYTHONPATH := ${SDDF}/tools/meta:${PYTHONPATH}
export PYTHONPATH

SUPPORTED_BOARDS := \
		maaxboard

include ${SDDF}/tools/make/board/common.mk

SDDF_CUSTOM_LIBC := 1
UTIL := $(SDDF)/util
LIBCO := $(SDDF)/libco
TOP := ${SDDF}/examples/tmu
SERIAL := $(SDDF)/serial
TIMER_DRIVER := $(SDDF)/drivers/timer/${TIMER_DRIV_DIR}
SERIAL_DRIVER := $(SDDF)/drivers/serial/${UART_DRIV_DIR}
TMU_DRIVER := $(SDDF)/drivers/tmu/${TMU_DRIV_DIR}

IMAGES :=\
	  client.elf \
	  timer_driver.elf \
	  serial_driver.elf \
	  serial_virt_tx.elf \
	  tmu_driver.elf

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group
CFLAGS +=  -Wno-unused-function -I${TOP}

IMAGE_FILE = loader.img
REPORT_FILE = report.txt
SYSTEM_FILE = tmu.system

DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
METAPROGRAM := $(TOP)/meta.py

CFLAGS += -I$(BOARD_DIR)/include \
	-I$(SDDF)/include \
	-I$(SDDF)/include/microkit \
	-I$(LIBCO) \
	-MD \
	-MP

CLIENT_OBJS := client.o

VPATH := ${TOP}
all: $(IMAGE_FILE)

client.o: client.c

client.elf: $(CLIENT_OBJS) libco.a libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client.data client.elf
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client.data client.elf
	touch $@

$(IMAGE_FILE) $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

${IMAGES}: libsddf_util_debug.a
.PHONY: all compile clean

clean::
	rm -f *.elf
	find . -name '*.[do]' |xargs --no-run-if-empty rm

clobber:: clean
	rm -f ${REPORT_FILE} ${IMAGE_FILE} *.a .*cflags*

include ${SDDF}/util/util.mk
include ${SERIAL}/components/serial_components.mk
include ${SERIAL_DRIVER}/serial_driver.mk
include ${TIMER_DRIVER}/timer_driver.mk
include ${LIBCO}/libco.mk
include ${TMU_DRIVER}/tmu_driver.mk
