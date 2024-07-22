#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile snippet builds the sound RX and TX virtualisers
# it should be included into your project Makefile
#
# NOTES:
#  Generates sound_virt.elf
#


SND_IMAGES := sound_virt.elf

CFLAGS_sound ?=

CHECK_SND_FLAGS_MD5:=.sound_cflags-$(shell echo -- $(CFLAGS) $(CFLAGS_sound) | shasum | sed 's/ *-//')

$(CHECK_SND_FLAGS_MD5):
	-rm -f .sound_cflags-*
	touch $@


sound_virt.elf: sound_virt.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

sound_virt.o: $(CHECK_SND_FLAGS_MD5)
sound_virt.o: $(SDDF)/sound/components/virt.c
	$(CC) $(CFLAGS) $(CFLAGS_sound) -o $@ -c $<

clean::
	rm -f sound_virt.[od] .sound_cflags-*

clobber::
	rm -f $(SND_IMAGES)


-include sound_virt.d
