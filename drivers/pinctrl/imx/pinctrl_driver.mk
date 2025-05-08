#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the iMX8 pinctrl driver
# Assumes libsddf_util_debug.a is in ${LIBS}.
#
# NOTES
#  Generates pinctrl_driver.elf
#  Has 3 parameters:
#    SDDF: path to sddf root
#    PYTHON: python interpreter
#    DTS: absolute path to the device tree source file.

ifndef PYTHON
$(error PYTHON is not set)
endif

ifndef DTS
$(error DTS is not set)
endif

PINCTRL_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

pinctrl/imx/pinctrl_config_data.s: ${DTS} ${PINCTRL_DIR}/create_pinctrl_config.py pinctrl/imx
	${PYTHON} ${PINCTRL_DIR}/create_pinctrl_config.py ${DTS} pinctrl/imx

pinctrl/imx/pinctrl_config_data.o: pinctrl/imx/pinctrl_config_data.s
	${CC} ${ASFLAGS} -c $< -o $@

pinctrl/imx/pinctrl.o: $(PINCTRL_DIR)/pinctrl.c pinctrl/imx
	${CC} ${CFLAGS} -DSOC_$(shell echo $(SOC) | tr a-z A-Z | tr - _) -c $< -o $@

pinctrl_driver.elf: pinctrl/imx/pinctrl.o pinctrl/imx/pinctrl_config_data.o
	${LD} ${LDFLAGS} $^ ${LIBS} -o $@

-include pinctrl/imx/pinctrl_driver.d

pinctrl/imx:
	mkdir -p $@

clean::
	rm -rf pinctrl

clobber::
	rm -f pinctrl