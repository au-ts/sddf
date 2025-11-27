# Snippet to build util library
#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# libsddf_util.a and libsddf_util_debug.a
# libsddf_util.a needs the component to have channels and queues
# with the the serial tx virtualiser, and for putchar to be initialised.
# libsddf_util_debug.a uses the microkit_dbg_puts function.
# Both are character at a time polling (i.e., slow, and only for debugging)

ifeq ($(strip $(ARCH)),)
$(error ARCH must be specified)
endif

OBJS_LIBUTIL := cache.o sddf_printf.o assert.o bitarray.o fsmalloc.o

ifeq ($(strip $(SDDF_CUSTOM_LIBC)),1)
	CFLAGS += -I${SDDF}/include/sddf/util/custom_libc
	OBJS_LIBUTIL += custom_libc/libc.o custom_libc/memcmp.o custom_libc/memcpy.o \
					custom_libc/memset.o custom_libc/strcmp.o custom_libc/strcpy.o \
					custom_libc/strlen.o custom_libc/strncmp.o
	ifeq ($(ARCH),riscv64)
		OBJS_LIBUTIL += custom_libc/memmove.o
	endif
endif

ifeq ($(ARCH),riscv64)
	CFLAGS += -I${SDDF}/util/custom_libc/riscv64
endif

ALL_OBJS_LIBUTIL := $(addprefix util/, ${OBJS_LIBUTIL} putchar_debug.o putchar_serial.o)

BASE_OBJS_LIBUTIL := $(addprefix util/, ${OBJS_LIBUTIL})
${ALL_OBJS_LIBUTIL}: |util util/custom_libc

libsddf_util_debug.a: ${BASE_OBJS_LIBUTIL} util/putchar_debug.o
	${RM} $@
	${AR} crv $@ $^
	${RANLIB} $@

libsddf_util.a: ${BASE_OBJS_LIBUTIL} util/putchar_serial.o
	${RM} $@
	${AR} crv $@ $^
	${RANLIB} $@

util/sddf_printf.o: ${SDDF}/util/printf.c | $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

util/%.o: ${SDDF}/util/%.c | $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

util/custom_libc/%.o: ${SDDF}/util/custom_libc/%.c | $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

util/custom_libc/%.o: ${SDDF}/util/custom_libc/${ARCH}/%.S
	${CC} ${CFLAGS} -c -o $@ $<

util/custom_libc/%.o: ${SDDF}/util/custom_libc/${ARCH}/%.c | $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

util:
	mkdir -p $@

util/custom_libc:
	mkdir -p $@

clean::
	${RM} -f ${ALL_OBJS_LIBUTIL} ${ALL_OBJS_LIBUTIL:.o=.d}

clobber:: clean
	${RM} -f libsddf_util.a libsddf_util_debug.a
	rmdir util

-include ${ALL_OBJS_LIBUTIL:.o=.d}
