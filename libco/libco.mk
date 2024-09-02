#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this make snippet to buid libco,a, a simple coroutine library.

LIBCO_DIR := $(abspath $(dir $(lastword ${MAKEFILE_LIST})))

libco/libco.o: $(LIBCO_DIR)/libco.c ${CHECK_FLAGS_BOARD_MD5} |libco
	${CC} ${CFLAGS} -c -o $@ $<

libco.a: libco/libco.o
	${AR} crv $@ $^
	${RANLIB} $@

libco:
	mkdir -p $@

-include libco/libco.d
