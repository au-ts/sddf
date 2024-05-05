#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the i2c virtualiser
#
# NOTES:
#  Builds i2c_virt.elf
#  Depends on ${SDDF}/util/util.mk also being included

i2c_virt.o: ${SDDF}/i2c/components/virt.c
	${CC} ${CFLAGS} -c -o $@ $<

i2c_virt.elf: i2c_virt.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@
