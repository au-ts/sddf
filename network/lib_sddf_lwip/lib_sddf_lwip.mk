#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile snippet builds the lib_sddf_lwip library
# The library provides a helper interface for using lwIP
# in an sDDF-net client. It also includes the necessary
# lwIP objects.
#
# NOTES:
# Generates lib_sddf_lwip.a or lib_sddf_lwip%.a. That is,
# it can generate different versions of the library with
# the same filename stem. This is useful if you want to
# build multiple different versions with different build-
# time configurations. CFLAGS can be configured using the
# SDDF_LWIP_CFLAGS variable, as well as its suffixed
# variant.
#
# For example, if you only need to generate one version
# of the library, usage is simple:
#
# LIB_SDDF_LWIP_CFLAGS := -O2
# include lib_sddf_lwip.mk
# my_program.elf: lib_sddf_lwip.a
#
# However, if you have two different programs requiring
# two differently configured versions of the library, you
# can do this instead:
#
# LIB_SDDF_LWIP_CFLAGS_0 := -O0 -g
# LIB_SDDF_LWIP_CFLAGS_1 := -O3
# include lib_sddf_lwip.mk
# program_0.elf: lib_sddf_lwip_0.a
# program_1.elf: lib_sddf_lwip_1.a
#

LIB_SDDF_LWIP_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

LWIPDIR := $(SDDF)/network/ipstacks/lwip/src
include $(LWIPDIR)/Filelists.mk

LIB_SDDF_LWIP_LWIP_FILES := \
	$(COREFILES) \
	$(CORE4FILES) \
	netif/ethernet.c \
	api/err.c

# Remove LWIPDIR prefix as we prefer the unprefixed form
LIB_SDDF_LWIP_LWIP_FILES := $(subst $(LWIPDIR)/,,$(LIB_SDDF_LWIP_LWIP_FILES))

lib_sddf_lwip.a: lib_sddf_lwip_out/lib_sddf_lwip.o $(addprefix lib_sddf_lwip_out/, $(LIB_SDDF_LWIP_LWIP_FILES:.c=.o))
	$(AR) rv $@ $^
	$(RANLIB) $@

lib_sddf_lwip%.a: lib_sddf_lwip_out%/lib_sddf_lwip.o $(addprefix lib_sddf_lwip_out%/, $(LIB_SDDF_LWIP_LWIP_FILES:.c=.o))
	$(AR) rv $@ $^
	$(RANLIB) $@

lib_sddf_lwip_out/lib_sddf_lwip.o: CFLAGS += $(LIB_SDDF_LWIP_CFLAGS)
lib_sddf_lwip_out/lib_sddf_lwip.o: $(CHECK_FLAGS_BOARD_MD5)
lib_sddf_lwip_out/lib_sddf_lwip.o: $(LIB_SDDF_LWIP_DIR)/lib_sddf_lwip.c | $(SDDF_LIBC_INCLUDE)
	mkdir -p $(dir $@)
	$(CC) $(CFLAGS) -c -o $@ $<

lib_sddf_lwip_out%/lib_sddf_lwip.o: CFLAGS += $(LIB_SDDF_LWIP_CFLAGS$*)
lib_sddf_lwip_out%/lib_sddf_lwip.o: $(CHECK_FLAGS_BOARD_MD5)
lib_sddf_lwip_out%/lib_sddf_lwip.o: $(LIB_SDDF_LWIP_DIR)/lib_sddf_lwip.c | $(SDDF_LIBC_INCLUDE)
	mkdir -p $(dir $@)
	$(CC) $(CFLAGS) -c -o $@ $<

$(foreach f,$(LIB_SDDF_LWIP_LWIP_FILES), \
	$(eval \
		lib_sddf_lwip_out/$(f:.c=.o): $(LWIPDIR)/$(f) | $$(SDDF_LIBC_INCLUDE) ; \
			mkdir -p $$(dir $$@); \
			$$(CC) $$(CFLAGS) $$(LIB_SDDF_LWIP_CFLAGS) -I$$(LWIPDIR)/include -c -o $$@ $$< \
	) \
	$(eval \
		lib_sddf_lwip_out%/$(f:.c=.o): $(LWIPDIR)/$(f) | $$(SDDF_LIBC_INCLUDE) ; \
			mkdir -p $$(dir $$@); \
			$$(CC) $$(CFLAGS) $$(LIB_SDDF_LWIP_CFLAGS$$*) -I$$(LWIPDIR)/include -c -o $$@ $$< \
	) \
)

clean::
	$(RM) -f lib_sddf_lwip_out/*

clobber:: clean
	$(RM) -f lib_sddf_lwip*.a

-include $(wildcard lib_sddf_lwip_out*/*.d)
-include $(wildcard lib_sddf_lwip_out*/core/*.d)
-include $(wildcard lib_sddf_lwip_out*/core/ipv4/*.d)
-include $(wildcard lib_sddf_lwip_out*/api/*.d)
-include $(wildcard lib_sddf_lwip_out*/netif/*.d)
