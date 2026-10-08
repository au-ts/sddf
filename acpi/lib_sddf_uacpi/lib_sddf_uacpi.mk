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
KERNEL_API_DIR := $(LIB_SDDF_UACPI_DIR)/kernel_api

UACPI_DIR := $(SDDF)/acpi/uacpi
UACPI_SRC_DIR := $(UACPI_DIR)/source
UACPI_INC_DIR := $(UACPI_DIR)/include

# uACPI uses CMake and Meson so we need to manually include the sources
UACPI_SOURCES := $(wildcard $(UACPI_SRC_DIR)/*.c)

# Remove UACPI_SRC_DIR prefix as we prefer the unprefixed form
UACPI_SOURCES := $(subst $(UACPI_SRC_DIR)/,,$(UACPI_SOURCES))

# Implementation of the OS layer for uACPI
KERNEL_API_SOURCES := event.c ioport.c stubs.c pci.c

lib_sddf_uacpi.a: \
	lib_sddf_uacpi_out/lib_sddf_uacpi.o \
	lib_sddf_uacpi_out/information.o \
	$(addprefix lib_sddf_uacpi_out/kernel_api/, $(KERNEL_API_SOURCES:.c=.o)) \
	$(addprefix lib_sddf_uacpi_out/uacpi/, $(UACPI_SOURCES:.c=.o))

	$(AR) crv $@ $^
	$(RANLIB) $@

lib_sddf_uacpi_out/lib_sddf_uacpi.o: $(LIB_SDDF_UACPI_DIR)/lib_sddf_uacpi.c | $(SDDF_LIBC_INCLUDE)
	mkdir -p $(dir $@)
	$(CC) $(CFLAGS) -I$(UACPI_INC_DIR) -c -o $@ $<

lib_sddf_uacpi_out/information.o: $(LIB_SDDF_UACPI_DIR)/information.c | $(SDDF_LIBC_INCLUDE)
	mkdir -p $(dir $@)
	$(CC) $(CFLAGS) -I$(UACPI_INC_DIR) -c -o $@ $<

$(foreach f,$(UACPI_SOURCES), \
	$(eval \
		lib_sddf_uacpi_out/uacpi/$(f:.c=.o): $(UACPI_SRC_DIR)/$(f); \
			mkdir -p $$(dir $$@); \
			$$(CC) $$(CFLAGS) -I$$(UACPI_INC_DIR) -c -o $$@ $$< \
	) \
)

$(foreach f,$(KERNEL_API_SOURCES), \
	$(eval \
		lib_sddf_uacpi_out/kernel_api/$(f:.c=.o): $(KERNEL_API_DIR)/$(f); \
			mkdir -p $$(dir $$@); \
			$$(CC) $$(CFLAGS) -I$$(UACPI_INC_DIR) -c -o $$@ $$< \
	) \
)

clean::
	$(RM) -f lib_sddf_uacpi_out/*

clobber:: clean
	$(RM) -f lib_sddf_uacpi.a

-include $(wildcard lib_sddf_uacpi_out*/*.d)

