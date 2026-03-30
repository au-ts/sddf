#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the timer virtualiser
#
# NOTES:
#  Builds timer_virt.elf
#  Depends on ${SDDF}/util/util.mk also being included

timer_heap.o: ${SDDF}/timer/components/timer_heap.c | $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

timer_virt.o: ${SDDF}/timer/components/timer_virt.c | $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

timer_virt.elf: timer_virt.o timer_heap.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@
