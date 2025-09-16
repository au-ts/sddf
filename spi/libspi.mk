#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this make snippet to build libspi.a
# Requires libmicrokitco to be available
#
# Required variables:
#   LIBMICROKITCO_INCLUDE_DIR - Path to libmicrokitco include directory
#   LIBMICROKITCO_OPTS_DIR - Path to directory containing libmicrokitco_opts.h

ifeq ($(strip $(LIBMICROKITCO_INCLUDE_DIR)),)
$(error LIBMICROKITCO_INCLUDE_DIR must be specified for libspi)
endif

ifeq ($(strip $(LIBMICROKITCO_OPTS_DIR)),)
$(error LIBMICROKITCO_OPTS_DIR must be specified for libspi)
endif

LIBSPI_DIR := $(SDDF)/spi
LIBSPI_OBJ := libspi.o

libspi.o: $(LIBSPI_DIR)/libspi.c
	$(CC) $(CFLAGS) -c -I$(SDDF)/include -I$(SDDF)/include/microkit -I$(LIBMICROKITCO_INCLUDE_DIR) -I$(LIBMICROKITCO_OPTS_DIR) -o $@ $<

libspi.a: $(LIBSPI_OBJ)
	$(AR) crv $@ $(LIBSPI_OBJ)
	$(RANLIB) $@

-include $(LIBSPI_OBJ:.o=.d)
