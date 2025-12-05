#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the OpenTitan i2c driver
#
# NOTES
# Generates i2c_driver.elf
# Requires libsddf_util_debug.a in ${ LIBS }

I2C_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

i2c_driver.elf: i2c/i2c_driver.o i2c/i2c_common.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

i2c/i2c_driver.o: CFLAGS+=-I${I2C_DRIVER_DIR}
i2c/i2c_driver.o: ${I2C_DRIVER_DIR}/i2c.c |i2c $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

i2c/i2c_common.o: CFLAGS+=-I${I2C_DRIVER_DIR}
i2c/i2c_common.o: ${I2C_DRIVER_DIR}/../i2c_common.c |i2c $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -c -o $@ $<

i2c:
	mkdir -p $@

clean::
	rm -rf i2c

clobber::
	rm -f i2c_driver.elf

-include i2c_driver.d
