# Snippet to build util library
#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# sddf_libutil.a and sddf_libutil_debug.a
# sddf_libutil.a needs the component to have channels and queues
# with the the serial_tx_virt and for putchar to be initialised.
# sddf_libutil_debug.a uses the microkit_dbg_putc function.
# Both are character at a time polling (i.e., slow, and only for debugging)

OBJS_LIBUTIL := cache.o sddf_printf.o newlibc.o assert.o bitarray.o fsmalloc.o

ALL_OBJS_LIBUTIL := $(addprefix util/, ${OBJS_LIBUTIL} putchar_debug.o putchar_serial.o)

BASE_OBJS_LIBUTIL := $(addprefix util/, ${OBJS_LIBUTIL})
${ALL_OBJS_LIBUTIL}: ${CHECK_FLAGS_BOARD_MD5} |util

libsddf_util_debug.a: ${BASE_OBJS_LIBUTIL} util/putchar_debug.o
	${AR} crv $@ $^
	${RANLIB} $@

libsddf_util.a: ${BASE_OBJS_LIBUTIL} util/putchar_serial.o
	${AR} crv $@ $^
	${RANLIB} $@

util/sddf_printf.o: ${SDDF}/util/printf.c
	${CC} ${CFLAGS} -c -o $@ $<

util/%.o: ${SDDF}/util/%.c
	${CC} ${CFLAGS} -c -o $@ $<

util:
	mkdir -p $@

clean::
	${RM} -f ${ALL_OBJS_LIBUTIL} ${ALL_OBJS_LIBUTIL:.o=.d}

clobber:: clean
	${RM} -f libsddf_util.a libsddf_util_debug.a
	rmdir util

-include ${ALL_OBJS_LIBUTIL:.o=.d}
