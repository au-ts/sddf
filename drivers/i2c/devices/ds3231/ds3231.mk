#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
DS3231_DRIVER := $(SDDF)/drivers/i2c/devices/ds3231

ds3231.o: ${DS3231_DRIVER}/ds3231.c ${DS3231_DRIVER}/ds3231.h
	${CC} ${CFLAGS} -c -o $@ $<
