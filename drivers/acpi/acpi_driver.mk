#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the ACPI driver
#
# NOTES:
#  Generates acpi_driver.elf
#  Expects libsddf_util_debug.a to be in ${LIBS}

ACPI_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

acpi_driver.elf: acpi/acpi.o acpi/interpreter.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

acpi/%.o: ${ACPI_DIR}/%.c ${ACPI_DIR}/interpreter.o ${CHECK_FLAGS_BOARD_MD5} |acpi $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -o $@ -c $^

acpi:
	mkdir -p acpi

clean::
	rm -rf acpi
clobber::
	rm -f acpi_driver.elf
