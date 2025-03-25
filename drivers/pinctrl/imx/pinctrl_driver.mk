#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 pinctrl driver
#
# NOTES
#  Generates pinctrl.elf
#  Has 4 parameters:
#    SDDF: path to sddf root
#    PYTHON
#    DTS_FILE: absolute path to the device tree source file.
#    SOC: System-on-Chip name that referenced by the pinmux device in DTS.
#    PINMUX_DEVICE: name of the pinmux device in DTS, e.g. imx8mq calls it "iomuxc" whereas imx8mm calls it "pinctrl"

#  Expects variable iomuxc_device to be set in the system description file to the
#    mapped address of the I/O Mux controller.

#  Expects variable iomuxc_gpr to be set in the system description file to the
#    mapped address of the General Purpose Registers (GPR) of the Mux controller.

#  These two memory region must be contiguous, with iomuxc_device coming before iomuxc_gpr.

ifndef PYTHON
$(error PYTHON is not set)
endif

ifndef DTS_FILE
$(error DTS_FILE is not set)
endif

ifndef PINMUX_DEVICE
$(error PINMUX_DEVICE is not set)
endif

ifndef SOC
$(error SOC is not set)
endif

ifeq (imx8mm-evk,$(findstring imx8mm-evk,$(SOC)))
else ifeq (imx8mq-evk,$(findstring imx8mq-evk,$(SOC)))
else ifeq (imx8mp-evk,$(findstring imx8mp-evk,$(SOC)))
else
$(error Pinctrl driver: unsupported SoC: $(SOC))
endif

PINCTRL_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

CHIP_HEADER_INC := -I$(SDDF)/drivers/pinctrl/imx

pinctrl_driver.elf: pinctrl/pinctrl.o pinctrl/pinctrl_config_data.o
	${LD} ${LDFLAGS} $^ ${LIBS} -o $@

pinctrl/pinctrl.o: $(PINCTRL_DIR)/pinctrl.c pinctrl
	${CC} ${CFLAGS} ${CHIP_HEADER_INC} -DCONFIG_DEBUG_BUILD -DSOC_$(shell echo $(SOC) | tr a-z A-Z | tr - _) -c $< -o $@

pinctrl/pinctrl_config_data.o: pinctrl/pinctrl_config_data.S
	${AS} ${ASFLAGS} $< -o $@

pinctrl/pinctrl_config_data.S: ${DTS_FILE} ${PINCTRL_DIR}/create_pinctrl_config.py
	${PYTHON} ${PINCTRL_DIR}/create_pinctrl_config.py ${SOC} ${DTS_FILE} ${PINMUX_DEVICE} pinctrl

pinctrl:
	mkdir -p pinctrl

clean::
	rm -rf pinctrl
clobber::
	rm -f pinctrl_driver.elf