#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
PN532_DRIVER := $(SDDF)/drivers/i2c/devices/pn532

pn532.o: ${PN532_DRIVER}/pn532.c ${PN532_DRIVER}/pn532.h
	${CC} ${CFLAGS} -c -o $@ $<

