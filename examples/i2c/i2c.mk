#
# Copyright 2023, UNSW
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

SUPPORTED_BOARDS := odroidc4

SDDF_CUSTOM_LIBC := 1
include ${SDDF}/tools/make/sddf.mk

TOP := $(SDDF)/examples/i2c
LIBCO := $(SDDF)/libco
PN532_DRIVER := $(SDDF)/i2c/devices/pn532
DS3231_DRIVER := $(SDDF)/i2c/devices/ds3231

IMAGES := i2c_virt.elf \
	  i2c_driver.elf \
	  client_pn532.elf \
	  client_ds3231.elf \
	  timer_driver.elf \
	  serial_driver.elf \
	  serial_virt_tx.elf
LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group
CFLAGS +=  -Wno-unused-function -I${TOP}

IMAGE_FILE = loader.img
REPORT_FILE = report.txt
SYSTEM_FILE = i2c.system

DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
METAPROGRAM := $(TOP)/meta.py

CFLAGS += -I$(BOARD_DIR)/include \
	-I$(SDDF)/include \
	-I$(SDDF)/include/microkit \
	-I$(LIBCO) \
	-DLIBI2C_RAW \
	-MD \
	-MP

CLIENT_PN532_OBJS := pn532.o client_pn532.o
DEPS_PN532 := $(CLIENT_PN532_OBJS:.o=.d)

CLIENT_DS3231_OBJS := ds3231.o client_ds3231.o
DEPS_DS3231 := $(CLIENT_DS3231_OBJS:.o=.d)

VPATH := ${TOP}
all: $(IMAGE_FILE)

client_pn532.elf: $(CLIENT_PN532_OBJS) libco.a libsddf_util.a libi2c.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

client_ds3231.elf: $(CLIENT_DS3231_OBJS) libco.a libsddf_util.a libi2c.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .device_resources=i2c_driver_device_resources.data i2c_driver.elf
	$(OBJCOPY) --update-section .i2c_driver_config=i2c_driver.data i2c_driver.elf
	$(OBJCOPY) --update-section .i2c_virt_config=i2c_virt.data i2c_virt.elf
	$(OBJCOPY) --update-section .i2c_client_config=i2c_client_client_ds3231.data client_ds3231.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client_ds3231.data client_ds3231.elf
	$(OBJCOPY) --update-section .i2c_client_config=i2c_client_client_pn532.data client_pn532.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client_pn532.data client_pn532.elf
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client_pn532.data client_pn532.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client_ds3231.data client_ds3231.elf
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

include ${LIBCO}/libco.mk
include ${PN532_DRIVER}/pn532.mk
include ${DS3231_DRIVER}/ds3231.mk
-include $(DEPS_DS3231)
-include $(DEPS_PN532)
