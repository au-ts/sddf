#
# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build the NVMe driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

BLK_DRIVER_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
BLK_NEED_TIMER := 1

CHECK_NVME_FLAGS_MD5:=.nvme_cflags-$(shell echo -- ${CFLAGS} | shasum | sed 's/ *-//')

${CHECK_NVME_FLAGS_MD5}:
	-rm -f .nvme_cflags-*
	touch $@

blk_driver.elf: blk_driver.o blk_driver_debug.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

blk_driver.o: ${BLK_DRIVER_DIR}/nvme.c ${CHECK_NVME_FLAGS_MD5}
	$(CC) -c $(CFLAGS) -I${BLK_DRIVER_DIR} -o $@ $<

blk_driver_debug.o: ${BLK_DRIVER_DIR}/nvme_debug.c ${CHECK_NVME_FLAGS_MD5}
	$(CC) -c $(CFLAGS) -I${BLK_DRIVER_DIR} -o $@ $<

-include blk_driver.d
-include blk_driver_debug.d

clean::
	rm -f blk_driver.o blk_driver_debug.o

clobber::
	rm -f blk_driver.elf
