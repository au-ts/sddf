#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile snippet builds the blk virtualiser
# it should be included into your project Makefile
#
# NOTES:
#  Generates blk_virt.elf
#


BLK_IMAGES := blk_virt.elf

CFLAGS_blk ?=

CHECK_BLK_FLAGS_MD5:=.blk_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_blk} | shasum | sed 's/ *-//')

${CHECK_BLK_FLAGS_MD5}:
	-rm -f .blk_cflags-*
	touch $@


blk_virt.elf: blk_virt.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

blk_virt.o: ${CHECK_BLK_FLAGS_MD5}
blk_virt.o: ${SDDF}/blk/components/virt.c
	${CC} ${CFLAGS} ${CFLAGS_blk} -o $@ -c $<

clean::
	rm -f blk_virt.[od] .blk_cflags-*

clobber::
	rm -f ${BLK_IMAGES}


-include blk_virt.d
