#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

timer_virt.elf: timer/components/virt.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

timer/components/virt.o: $(SDDF)/timer/components/virt.c $(CHECK_FLAGS_BOARD_HASH) | $(SDDF_LIBC_INCLUDE)
	mkdir -p $(@D)
	$(CC) $(CFLAGS) -MMD -MP -c $< -o $@

-include timer/components/virt.d

clean::
	rm -f timer/components/virt.o timer/components/virt.d

clobber:: clean
	rm -f timer_virt.elf
