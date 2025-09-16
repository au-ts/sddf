#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip $(LIBMICROKITCO_OPTS_DIR)),)
$(error LIBMICROKITCO_OPTS_DIR must be specified for w25qxx)
endif

W25QXX_DRIVER := $(SDDF)/spi/devices/w25qxx

w25qxx.o: ${W25QXX_DRIVER}/w25qxx.c
	${CC} ${CFLAGS} -I$(LIBMICROKITCO_OPTS_DIR) -c -o $@ $<
