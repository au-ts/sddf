#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
W25QXX_DRIVER := $(SDDF)/spi/devices/w25qxx

w25qxx.o: ${W25QXX_DRIVER}/w25qxx.c
	${CC} ${CFLAGS} -c -o $@ $<

