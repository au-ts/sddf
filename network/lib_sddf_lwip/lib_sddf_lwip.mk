#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(MAX_NUM_BUFFS)),)
$(error MAX_NUM_BUFFS must be specified)
endif

CFLAGS += -DMAX_NUM_BUFFS=$(MAX_NUM_BUFFS)

LIB_SDDF_LWIP_DIR := ${SDDF}/network/lib_sddf_lwip
LIB_SDDF_LWIP_FILES := $(addprefix ${LIB_SDDF_LWIP_DIR}/, lib_sddf_lwip.c)
LIB_SDDF_LWIP_OBJS := $(LIB_SDDF_LWIP_FILES:.c=.o)

${LIB_SDDF_LWIP_OBJS}: | ${LIB_SDDF_LWIP_DIR} ${CHECK_FLAGS_BOARD_MD5}
${LIB_SDDF_LWIP_DIR}:
	mkdir -p $@

lib_sddf_lwip.a: ${LIB_SDDF_LWIP_OBJS}
	${AR} rv $@ $^
	${RANLIB} $@

clean::
	${RM} -f ${LIB_SDDF_LWIP_OBJS} ${LIB_SDDF_LWIP_OBJS:.o=.d}

clobber:: clean
	${RM} -f lib_sddf_lwip.a
	rmdir ${LIB_SDDF_LWIP_DIR}

-include ${LIB_SDDF_LWIP_OBJS:.o=.d}
