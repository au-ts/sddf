#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build the IMX8 uSDHC driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

USDHC_DRIVER_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

blk_driver.elf: blk/mmc/imx/blk_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

blk/mmc/imx/blk_driver.o: ${USDHC_DRIVER_DIR}/usdhc.c |blk/mmc/imx
	$(CC) -c $(CFLAGS) -o $@ $<

-include blk_driver.d

blk/mmc/imx:
	mkdir -p $@

clean::
	rm -f blk/mmc/imx/blk_driver.[do]

clobber::
	rm -rf blk/mmc
