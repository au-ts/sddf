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
#  Has 3 parameters: 
#    PYTHON
#    DTS_FILE: absolute path to the device tree source file.
#    SOC: System-on-Chip name that referenced by the pinmux device in DTS.

#  Expects variable pinctrl_ao_base to be set in the system description file to the
#    mapped address of the pinmux controller of the Always-On domain.

#  Expects variable pinctrl_periphs_base to be set in the system description file to the
#    mapped address of the peripherals pinmux controller.

ifndef PYTHON
$(error PYTHON is not set)
endif

ifndef DTS_FILE 
$(error DTS_FILE is not set)
endif

ifndef SOC 
$(error SOC is not set)
endif

ifeq (amlogic\,sm1,$(findstring amlogic\,sm1,$(SOC)))
else
$(error Pinctrl driver: unsupported SoC: $(SOC))
endif

PINCTRL_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

pinctrl_driver.elf: pinctrl/pinctrl.o pinctrl/pinctrl_config_data.o
	${LD} ${LDFLAGS} $? ${LIBS} -o $@

pinctrl/pinctrl.o: $(PINCTRL_DIR)/pinctrl.c pinctrl
	${CC} ${CFLAGS} -DCONFIG_DEBUG_BUILD -c $< -o $@

pinctrl/pinctrl_config_data.o: pinctrl/pinctrl_config_data.s
	${AS} $< -o $@

pinctrl/pinctrl_config_data.s:
	${PYTHON} ${PINCTRL_DIR}/create_pinctrl_config.py ${SOC} ${DTS_FILE} pinctrl

pinctrl: 
	mkdir -p pinctrl

clean::
	rm -rf pinctrl
clobber::
	rm -f pinctrl_driver.elf
