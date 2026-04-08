#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := clang
endif

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
UTIL := $(SDDF)/util

SUPPORTED_BOARDS := \
		maaxboard

include ${SDDF}/tools/make/board/common.mk

SDDF_CUSTOM_LIBC := 1
I2C := $(SDDF)/i2c
UTIL := $(SDDF)/util
LIBCO := $(SDDF)/libco
TOP := ${SDDF}/examples/thermal_control
SERIAL := $(SDDF)/serial
I2C_DRIVER := $(SDDF)/drivers/i2c/${I2C_DRIV_DIR}
SERIAL_DRIVER := $(SDDF)/drivers/serial/${UART_DRIV_DIR}
CLK_DRIVER := $(SDDF)/drivers/clk/${CLK_DRIV_DIR}
TIMER_DRIVER := $(SDDF)/drivers/timer/${TIMER_DRIV_DIR}
DVFS_DRIVER := $(SDDF)/drivers/dvfs/${DVFS_DRIV_DIR}
PMIC_DRIVER := $(SDDF)/drivers/pmic/${PMIC_DRIV_DIR}
PWM_DRIVER := $(SDDF)/drivers/pwm/${PWM_DRIV_DIR}
PINCTRL_DRIVER := $(SDDF)/drivers/pinctrl/${PINCTRL_DRIV_DIR}
TMU_DRIVER := $(SDDF)/drivers/tmu/${TMU_DRIV_DIR}

# HACK for Pinctrl
ASFLAGS := -target aarch64-none-elf

IMAGES := timer_driver.elf \
		  clk_driver.elf \
		  dvfs_driver.elf \
		  pmic_driver.elf \
		  i2c_driver.elf \
		  i2c_virt.elf \
		  thermal_control.elf \
		  serial_driver.elf \
		  serial_virt_tx.elf \
		  pwm_driver.elf \
		  pinctrl_driver.elf \
		  tmu_driver.elf \
		  worker.elf

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

IMAGE_FILE := loader.img
REPORT_FILE := report.txt
SYSTEM_FILE = thermal_control.system
THERMAL_CONTROL_OBJS := thermal_control.o

DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
METAPROGRAM := $(TOP)/meta.py

CFLAGS += -I$(BOARD_DIR)/include \
	-I$(SDDF)/include \
	-I$(SDDF)/include/microkit \
	-I$(LIBCO) \
	-DLIBI2C_NOCO \
	-MD \
	-MP

VPATH := ${TOP}
all: $(IMAGE_FILE)

${IMAGES}: libsddf_util_debug.a

thermal_control.o: ${TOP}/thermal_control.c
	$(CC) -c $(CFLAGS) $(CHIP_HEADER_INC) -DTEST_BOARD_${MICROKIT_BOARD} $< -o thermal_control.o

thermal_control.elf: thermal_control.o libco.a libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

worker.o: ${TOP}/worker.c
	$(CC) -c $(CFLAGS) $(CHIP_HEADER_INC) -DTEST_BOARD_${MICROKIT_BOARD} $< -o worker.o

worker.elf: worker.o libco.a libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@


$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_thermal_control.data thermal_control.elf
	$(OBJCOPY) --update-section .i2c_client_config=i2c_client_pmic_driver.data pmic_driver.elf
	$(OBJCOPY) --update-section .device_resources=i2c_driver_device_resources.data i2c_driver.elf
	$(OBJCOPY) --update-section .i2c_driver_config=i2c_driver.data i2c_driver.elf
	$(OBJCOPY) --update-section .i2c_virt_config=i2c_virt.data i2c_virt.elf
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_thermal_control.data thermal_control.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_worker.data worker.elf
	$(OBJCOPY) --update-section .device_resources=pinctrl_driver_device_resources.data pinctrl_driver.elf
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
include ${CLK_DRIVER}/clk_driver.mk
include ${DVFS_DRIVER}/dvfs_driver.mk
include ${PMIC_DRIVER}/pmic_driver.mk
include ${I2C}/libi2c.mk
include ${I2C}/components/i2c_virt.mk
include ${I2C_DRIVER}/i2c_driver.mk
include ${PWM_DRIVER}/pwm_driver.mk
include ${PINCTRL_DRIVER}/pinctrl_driver.mk
include ${TMU_DRIVER}/tmu_driver.mk
include ${LIBCO}/libco.mk
