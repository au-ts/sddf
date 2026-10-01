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
#  Assumes libsddf_util_debug.a is in ${LIBS} and built with SDDF_TLSF_MALLOC=1.

ACPI_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

LIB_SDDF_UACPI_DIR := $(ACPI_DIR)/../../acpi/lib_sddf_uacpi

include $(LIB_SDDF_UACPI_DIR)/lib_sddf_uacpi.mk

acpi_driver.elf: acpi/acpi.o lib_sddf_uacpi.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

acpi/%.o: ${ACPI_DIR}/%.c ${CHECK_FLAGS_BOARD_MD5} |acpi $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -o $@ -c $^

acpi:
	mkdir -p acpi

clean::
	rm -rf acpi
clobber::
	rm -f acpi_driver.elf
