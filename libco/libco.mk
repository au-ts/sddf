#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this make snippet to build libco,a, a simple coroutine library.

LIBCO_DIR := $(abspath $(dir $(lastword ${MAKEFILE_LIST})))

libco/libco.o: $(LIBCO_DIR)/libco.c |libco $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

libco.a: libco/libco.o
	${AR} crv $@ $^
	${RANLIB} $@

libco:
	mkdir -p $@

-include libco/libco.d
