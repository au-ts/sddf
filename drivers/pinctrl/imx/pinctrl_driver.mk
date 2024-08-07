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
#  Expects variable iomuxc_base to be set in the system description file to the
#      mapped address of the I/O Mux controller.

PINCTRL_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

pinctrl_driver.elf: pinctrl pinctrl/pinctrl.o pinctrl/pinctrl_config_data.o
	$(LD) $(LDFLAGS) $? $(LIBS) -o $@

pinctrl/pinctrl.o: $(PINCTRL_DIR)/pinctrl.c
	${CC} ${CFLAGS} -c $< -o $@

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
