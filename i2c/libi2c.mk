#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this make snippet to build libi2c.a
# Requires libmicrokitco to be available - use libi2c_raw.mk if unavailable.
#
# Required variables:
#   LIBMICROKITCO_INCLUDE_DIR - Path to libmicrokitco include directory
#   LIBMICROKITCO_OPTS_DIR - Path to directory containing libmicrokitco_opts.h

# If we are using the raw API, we don't need libmicrokitco
ifneq ($(LIBI2C_RAW),)
ifeq ($(strip $(LIBMICROKITCO_INCLUDE_DIR)),)
$(error LIBMICROKITCO_INCLUDE_DIR must be specified for libi2c)
endif

ifeq ($(strip $(LIBMICROKITCO_OPTS_DIR)),)
$(error LIBMICROKITCO_OPTS_DIR must be specified for libi2c)
endif
CFLAGS += -I$(LIBMICROKITCO_INCLUDE_DIR) -I$(LIBMICROKITCO_OPTS_DIR)
endif

LIBI2C_DIR := $(SDDF)/i2c
LIBI2C_OBJ := libi2c.o

libi2c.o: $(LIBI2C_DIR)/libi2c.c
	$(CC) $(CFLAGS) -c  -o $@ $<

libi2c.a: $(LIBI2C_OBJ)
	$(AR) crv $@ $(LIBI2C_OBJ)
	$(RANLIB) $@

-include $(LIBI2C_OBJ:.o=.d)
