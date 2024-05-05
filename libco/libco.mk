#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this make snippet to buid libco,a, a simple coroutine library.

CHECK_LIBCO_FLAGS_MD5:=.libco_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | md5sum | sed 's/  *-//')

${CHECK_LIBCO_FLAGS_MD5}:
	-rm -f .libco_cflags-*
	touch $@

libco.o: $(LIBCO)/libco.c ${CHECK_LIBCO_FLAGS_MD5}
	${CC} ${CFLAGS} -c -o $@ $<

libco.a: libco.o
	ar cr $@ $^

-include libco.d
