#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
PN532_DRIVER := $(SDDF)/i2c/devices/pn532

pn532.o: ${PN532_DRIVER}/pn532.c
	${CC} ${CFLAGS} -c -o $@ $<
