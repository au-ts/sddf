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
#  Has X parameters: TODO
#  Expects variable iomuxc_device to be set in the system description file to the
#    mapped address of the I/O Mux controller.
#  Expects variable iomuxc_gpr to be set in the system description file to the
#    mapped address of the General Purpose Registers (GPR) of the Mux controller.
#  These two memory region must be contiguous, with iomuxc_device coming before iomuxc_gpr.

PINCTRL_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

pinctrl_driver.elf: pinctrl/pinctrl.o pinctrl/pinctrl_config_data.o
	$(LD) $(LDFLAGS) $? $(LIBS) -o $@

pinctrl/pinctrl.o: $(PINCTRL_DIR)/pinctrl.c pinctrl
	${CC} ${CFLAGS} -DCONFIG_DEBUG_BUILD -c $< -o $@

pinctrl/pinctrl_config_data.o: pinctrl/pinctrl_config_data.s
	${AS} $< -o $@

pinctrl/pinctrl_config_data.s:
	python3 $(PINCTRL_DIR)/create_pinctrl_config.py imx8mq-evk $(TOP)/dts/maaxboard.dts pinctrl

pinctrl: 
	mkdir -p pinctrl

clean::
	rm -rf pinctrl
clobber::
	rm -f pinctrl_driver.elf
