#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the OdroidC4 pinctrl driver
#
# NOTES
#  Generates pinctrl.elf
#  Has 4 parameters: 
#    SDDF: path to sddf root
#    PYTHON
#    DTS_FILE: absolute path to the device tree source file.
#    SOC: System-on-Chip name that referenced by the pinmux device in DTS.

#  Expects variable pinctrl_ao_base to be set in the system description file to the
#    mapped address of the pinmux controller of the Always-On domain.
#  On OdroidC4 it is 0xFF80_0000 for 0x1000 size

#  Expects variable pinctrl_periphs_base to be set in the system description file to the
#    mapped address of the peripherals pinmux controller.
#  On OdroidC4 it is 0xFF63_4000 for 0x2000 size

ifndef PYTHON
$(error PYTHON is not set)
endif

ifndef DTS_FILE 
$(error DTS_FILE is not set)
endif

ifndef SOC 
$(error SOC is not set)
endif

ODROIDC4_DTS_STR := hardkernel,odroid-c4
ifeq ($(ODROIDC4_DTS_STR),$(findstring $(ODROIDC4_DTS_STR),$(SOC)))
else
$(error Pinctrl driver: unsupported SoC: $(SOC))
endif

PINCTRL_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

# Include this in your client as well
CHIP_HEADER_INC := -I$(SDDF)/include/sddf/pinctrl/board/meson

pinctrl_driver.elf: pinctrl/pinctrl.o pinctrl/pinctrl_config_data.o
	${LD} ${LDFLAGS} $^ ${LIBS} -o $@

pinctrl/pinctrl.o: $(PINCTRL_DIR)/pinctrl.c pinctrl
	${CC} ${CFLAGS} ${CHIP_HEADER_INC} -DCONFIG_DEBUG_BUILD -c $< -o $@

pinctrl/pinctrl_config_data.o: pinctrl/pinctrl_config_data.s
	${AS} ${ASFLAGS} $< -o $@

pinctrl/pinctrl_config_data.s: ${DTS_FILE} ${PINCTRL_DIR}/create_pinctrl_config.py
	${PYTHON} ${PINCTRL_DIR}/create_pinctrl_config.py ${SOC} ${DTS_FILE} pinctrl

pinctrl: 
	mkdir -p pinctrl

clean::
	rm -rf pinctrl
clobber::
	rm -f pinctrl_driver.elf