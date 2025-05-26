#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the spi virtualiser
#
# NOTES:
#  Builds spi_virt.elf
#  Depends on ${SDDF}/util/util.mk also being included

spi_virt.o: ${SDDF}/spi/components/virt.c
	${CC} ${CFLAGS} -c -o $@ $<

spi_virt.elf: spi_virt.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@
