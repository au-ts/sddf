#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the OpenTitan SPI driver
#
# NOTES:
#  Generates spi_driver.elf
#  Expects libsddf_util_debug.a in ${LIBS}

SPI_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

spi_driver.elf: spi/spi.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

spi/spi.o: ${SPI_DIR}/spi.c ${SPI_DIR}/driver.h ${CHECK_FLAGS_BOARD_MD5} |spi
	${CC} ${CFLAGS} -o $@ -c $<

spi:
	mkdir -p spi

clean::
	rm -rf spi
clobber::
	rm -f spi_driver.elf
