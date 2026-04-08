#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 NIC driver
#
# NOTES
#  Generates dvfs_driver.elf
#  Expects libsddf_util_debug.a to be in LIBS

DVFS_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

dvfs_driver.elf: dvfs/dvfs.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

dvfs/dvfs.o: ${DVFS_DRIVER_DIR}/dvfs.c ${CHECK_FLAGS_BOARD_MD5} |dvfs $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -o $@ -c $<

dvfs:
	mkdir -p dvfs

clean::
	rm -rf dvfs
clobber::
	rm -f dvfs_driver.elf
