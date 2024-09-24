#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build the IMX8 uSDHC driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.
# Requires usdhc_regs to be set to the mapped base of the uSDHC registers
# in the system description file.

USDHC_DRIVER_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

mmc_driver.elf: blk/mmc/imx/mmc_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

blk/mmc/imx/mmc_driver.o: ${USDHC_DRIVER_DIR}/usdhc.c |blk/mmc/imx
	$(CC) -c $(CFLAGS) -o $@ $<

-include mmc_driver.d

blk/mmc/imx:
	mkdir -p $@

clean::
	rm -f blk/mmc/imx/mmc_driver.[do]

clobber::
	rm -rf blk/mmc
