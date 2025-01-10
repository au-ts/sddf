#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

LIB_SDDF_LWIP_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

lib_sddf_lwip.o: CFLAGS += -DSDDF_LWIP_NUM_BUFS=$(SDDF_LWIP_NUM_BUFS)
lib_sddf_lwip.o: ${CHECK_FLAGS_BOARD_MD5}
lib_sddf_lwip.o: $(LIB_SDDF_LWIP_DIR)/lib_sddf_lwip.c
	${if ${SDDF_LWIP_NUM_BUFS},,${error "SDDF_LWIP_NUM_BUFS not defined"}}
	${CC} ${CFLAGS} -c -o $@ $<

lib_sddf_lwip%.o: CFLAGS += ${CFLAGS$*} -DSDDF_LWIP_NUM_BUFS=$(SDDF_LWIP_NUM_BUFS$*)
lib_sddf_lwip%.o: ${CHECK_FLAGS_BOARD_MD5}
lib_sddf_lwip%.o: $(LIB_SDDF_LWIP_DIR)/lib_sddf_lwip.c
	${if ${SDDF_LWIP_NUM_BUFS$*},,${error "SDDF_LWIP_NUM_BUFS$* not defined for $@"}}
	${CC} ${CFLAGS} -c -o $@ $<

lib_sddf_lwip.a: lib_sddf_lwip.o
	${AR} rv $@ $^
	${RANLIB} $@

lib_sddf_lwip%.a: lib_sddf_lwip%.o
	${AR} rv $@ $^
	${RANLIB} $@

clean::
	${RM} -f lib_sddf_lwip*.o

clobber:: clean
	${RM} -f lib_sddf_lwip*.a

-include ${wildcard lib_sddf_lwip*.d}
