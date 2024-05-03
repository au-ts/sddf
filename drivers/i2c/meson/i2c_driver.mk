#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson i2c driver

I2C_DRIVER_DIR := ${SDDF}/drivers/i2c/meson
i2c_driver.elf: i2c_driver.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

i2c_driver.o: CFLAGS+=-I${I2C_DRIVER_DIR} -DI2C_BUS_NUM=${I2C_BUS_NUM}
i2c_driver.o: ${I2C_DRIVER_DIR}/i2c.c
	${CC} ${CFLAGS} -c -o $@ $<

-include i2c_driver.d
