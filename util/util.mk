# Snippet to build util library
#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# sddf_libutil.a

OBJS := cache.o sddf_printf.o putchar_debug.o

sddf_libutil.a: ${OBJS}
	ar rv $@ ${OBJS}

VPATH += ${SDDF}/util

sddf_printf.o: ${SDDF}/util/printf.c
	${CC} ${CFLAGS} -c -o $@ $<

-include ${OBJS:.o=.d}
