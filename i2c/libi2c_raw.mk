#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
#
# libco must be built with this

LIBCO := $(SDDF)/libco

libi2c_raw.o: ${SDDF}/i2c/libi2c_raw.c
	${CC} ${CFLAGS} -c -I$(SDDF)/include -I${SDDF}/include/microkit -I$(SDDF)/include/sddf/i2c -I${LIBCO} -o $@ $<

libi2c_raw.a: libi2c_raw.o
	$(AR) crv $@ $^
	$(RANLIB) $@
