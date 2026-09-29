#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile snippet builds the lib_sddf_uacpi library
# The library provides all the "kernel" APIs and initialisation
# routines that uACPI requires before it can be called from
# other code. It also includes the necessary uACPI objects.
#
# USAGE:
#
# include lib_sddf_uacpi.mk
# my_acpi_driver.elf: lib_sddf_uacpi.a
#
# Assumes libsddf_util_debug.a is in ${LIBS} and built with SDDF_TLSF_MALLOC=1.

LIB_SDDF_UACPI_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

UACPI_DIR := $(SDDF)/acpi/uacpi
UACPI_SRC_DIR := $(UACPI_DIR)/source
UACPI_INC_DIR := $(UACPI_DIR)/include

# uACPI uses CMake and Meson so we need to manually include the sources
LIB_SDDF_UACPI_SOURCES := $(wildcard $(UACPI_SRC_DIR)/*.c)

# Remove UACPI_SRC_DIR prefix as we prefer the unprefixed form
LIB_SDDF_UACPI_SOURCES := $(subst $(UACPI_SRC_DIR)/,,$(LIB_SDDF_UACPI_SOURCES))

lib_sddf_uacpi.a: lib_sddf_uacpi_out/lib_sddf_uacpi.o lib_sddf_uacpi_out/stubs.o $(addprefix lib_sddf_uacpi_out/, $(LIB_SDDF_UACPI_SOURCES:.c=.o))
	$(AR) crv $@ $^
	$(RANLIB) $@

lib_sddf_uacpi_out/lib_sddf_uacpi.o: $(LIB_SDDF_UACPI_DIR)/lib_sddf_uacpi.c | $(SDDF_LIBC_INCLUDE)
	mkdir -p $(dir $@)
	$(CC) $(CFLAGS) -I$(UACPI_INC_DIR) -c -o $@ $<

lib_sddf_uacpi_out/stubs.o: $(LIB_SDDF_UACPI_DIR)/stubs.c | $(SDDF_LIBC_INCLUDE)
	mkdir -p $(dir $@)
	$(CC) $(CFLAGS) -I$(UACPI_INC_DIR) -c -o $@ $<

$(foreach f,$(LIB_SDDF_UACPI_SOURCES), \
	$(eval \
		lib_sddf_uacpi_out/$(f:.c=.o): $(UACPI_SRC_DIR)/$(f); \
			mkdir -p $$(dir $$@); \
			$$(CC) $$(CFLAGS) -I$$(UACPI_INC_DIR) -c -o $$@ $$< \
	) \
)

clean::
	$(RM) -f lib_sddf_uacpi_out/*

clobber:: clean
	$(RM) -f lib_sddf_uacpi.a

-include $(wildcard lib_sddf_uacpi_out*/*.d)

