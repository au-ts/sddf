#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8MQ pinctrl driver
#
# NOTES
#  Generates pinctrl.elf
#  Has 4 parameters: 
#    PYTHON
#    DTS_FILE: absolute path to the device tree source file.
#    SOC: System-on-Chip name that referenced by the pinmux device in DTS.
#    PINMUX_DEVICE: name of the pinmux device in DTS, e.g. imx8mq calls it "iomuxc" whereas imx8mm calls it "pinctrl"

#  Expects variable iomuxc_device to be set in the system description file to the
#    mapped address of the I/O Mux controller.

#  Expects variable iomuxc_gpr to be set in the system description file to the
#    mapped address of the General Purpose Registers (GPR) of the Mux controller.

#  These two memory region must be contiguous, with iomuxc_device coming before iomuxc_gpr.

PINCTRL_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

pinctrl_driver.elf: pinctrl/pinctrl.o pinctrl/pinctrl_config_data.o
	${LD} ${LDFLAGS} $? ${LIBS} -o $@

pinctrl/pinctrl.o: $(PINCTRL_DIR)/pinctrl.c pinctrl
	${CC} ${CFLAGS} -DCONFIG_DEBUG_BUILD -c $< -o $@

pinctrl/pinctrl_config_data.o: pinctrl/pinctrl_config_data.s
	${AS} $< -o $@

pinctrl/pinctrl_config_data.s:
	${PYTHON} ${PINCTRL_DIR}/create_pinctrl_config.py ${SOC} ${DTS_FILE} ${PINMUX_DEVICE} pinctrl

pinctrl: 
	mkdir -p pinctrl

clean::
	rm -rf pinctrl
clobber::
	rm -f pinctrl_driver.elf
