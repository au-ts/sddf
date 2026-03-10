#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson tmu driver
#
# NOTES
#  Generates tmu_driver.elf
#  Requires floating point support
#  Requires libsddf_util_debug.a in ${LIBS}

TMU_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

tmu_driver.elf: tmu/tmu_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

tmu/tmu_driver.o: CFLAGS+=-I${TMU_DRIVER_DIR}
tmu/tmu_driver.o: ${TMU_DRIVER_DIR}/tmu.c |tmu $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

tmu:
	mkdir -p $@

clean::
	rm -rf tmu

clobber::
	rm -f tmu_driver.elf

-include tmu_driver.d
