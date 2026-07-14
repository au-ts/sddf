#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson pmic driver
#
# NOTES
#  Generates pmic_driver.elf
#  Requires libsddf_util_debug.a in ${LIBS}
#  Requires libi2c.a

PMIC_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

pmic_driver.elf: pmic/pmic_driver.o libi2c.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

pmic/pmic_driver.o: CFLAGS+=-I${PMIC_DRIVER_DIR}
pmic/pmic_driver.o: ${PMIC_DRIVER_DIR}/bd71837.c |pmic $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

pmic:
	mkdir -p $@

clean::
	rm -rf pmic

clobber::
	rm -f pmic_driver.elf

-include pmic_driver.d
