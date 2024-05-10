# Snippet to build util library
#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#  
# Include this snippet in your project Makefile to build
# sddf_libutil.a and sddf_libutil_debug.a
# sddf_libutil.a needs access to the serial device, and
# a variable 'uart_base' to be set in the System Description File;
# sddf_libutil_debug.a uses the microkit_dbg_putc function.
# Both are character at a time polling (i.e., slow, and only for debugging)

OBJS_LIBUTIL := cache.o sddf_printf.o newlibc.o

libsddf_util_debug.a: ${OBJS_LIBUTIL} putchar_debug.o
	${AR} rv $@ $^
	ranlib $@

libsddf_util.a: ${OBJS_LIBUTIL} putchar_serial.o
	${AR} rv $@ $^
	ranlib $@

VPATH += ${SDDF}/util

sddf_printf.o: ${SDDF}/util/printf.c
	${CC} ${CFLAGS} -c -o $@ $<

clean::
	${RM} -f ${OBJS_LIBUTIL} ${OBJS_LIBUTIL:.o=.d} putchar_debug.[od] putchar_serial.[od]

clobber:: clean
	${RM} -f libsddf_util.a libsddf_util_debug.a

-include ${OBJS_LIBUTIL:.o=.d} putchar_debug.d putchar_serial.d
