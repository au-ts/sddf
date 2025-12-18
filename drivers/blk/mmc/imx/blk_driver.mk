#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build the IMX8 uSDHC driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

USDHC_DRIVER_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
CHECK_BLKDRV_FLAGS_MD5:=.blkdrv_cflags-$(shell echo -- ${CFLAGS} | shasum | sed 's/ *-//')

${CHECK_BLKDRV_FLAGS_MD5}:
	-rm -f .blkdrv_cflags-*
	touch $@

ifeq ($(PANCAKE_BLK_DRIVER),1)
blk_driver.elf: ${BUILD_DIR}/usdhc_pnk.o blk/mmc/imx/usdhc.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

USDHC_PNK = ${UTIL}/util.pnk \
		${USDHC_DRIVER_DIR}/usdhc.pnk

${BUILD_DIR}/usdhc_pnk.S: $(USDHC_PNK)
	cat $(USDHC_PNK) | cpp -P | $(CAKE_COMPILER) --target=arm8 --pancake --main_return=true > $@

blk/mmc/imx/usdhc.o: ${USDHC_DRIVER_DIR}/usdhc.c ${CHECK_BLKDRV_FLAGS_MD5} |blk/mmc/imx
	$(CC) -c $(CFLAGS) -DPANCAKE_BLK_DRIVER -I ${USDHC_DRIVER_DIR} -o $@ $<

${BUILD_DIR}/usdhc_pnk.o: ${BUILD_DIR}/usdhc_pnk.S
	$(CC) -c -mcpu=$(CPU) -target $(TARGET) $< -o $@
else
blk_driver.elf: blk/mmc/imx/blk_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

blk/mmc/imx/blk_driver.o: ${USDHC_DRIVER_DIR}/usdhc.c ${CHECK_BLKDRV_FLAGS_MD5} |blk/mmc/imx
	$(CC) -c $(CFLAGS) -I ${USDHC_DRIVER_DIR} -o $@ $<
endif

-include blk/mmc/imx/mmc_driver.d

blk/mmc/imx:
	mkdir -p $@

clean::
	rm -f blk/mmc/imx/blk_driver.[do] blk/mmc/imx/usdhc.[do]

clobber::
	rm -rf blk/mmc
