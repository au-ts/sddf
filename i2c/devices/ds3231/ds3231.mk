#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
DS3231_DRIVER := $(SDDF)/i2c/devices/ds3231

ds3231.o: ${DS3231_DRIVER}/ds3231.c
	${CC} ${CFLAGS} -c -o $@ $<
