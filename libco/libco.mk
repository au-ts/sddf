#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this make snippet to buid libco,a, a simple coroutine library.

LIBCO_DIR := $(abspath $(dir $(lastword ${MAKEFILE_LIST})))
CHECK_LIBCO_FLAGS_MD5:=.libco_cflags-$(shell echo -- ${CFLAGS} | shasum | sed 's/ *-//')

${CHECK_LIBCO_FLAGS_MD5}:
	-rm -f .libco_cflags-*
	touch $@

libco/libco.o: $(LIBCO_DIR)/libco.c ${CHECK_LIBCO_FLAGS_MD5} |libco
	${CC} ${CFLAGS} -c -o $@ $<

libco.a: libco/libco.o
	${AR} cr $@ $^
	${RANLIB} $@

libco:
	mkdir -p $@

-include libco/libco.d
