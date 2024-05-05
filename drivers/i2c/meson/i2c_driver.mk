#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson i2c driver
#
# NOTES
#  Generates i2c_driver.elf
#  Requires ${SDDF}/util/util.mk to be included
#  Has one parameter: I2C_BUS_NUM to select which bus is being driven
#  Needs three variables set in system description file:
#  i2c_bus --- the i2c controller
#  gpio --- the GPIO registers for the pinmux
#  clk --- the clock registers


I2C_DRIVER_DIR := ${SDDF}/drivers/i2c/meson
i2c_driver.elf: i2c_driver.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

i2c_driver.o: CFLAGS+=-I${I2C_DRIVER_DIR} -DI2C_BUS_NUM=${I2C_BUS_NUM}
i2c_driver.o: ${I2C_DRIVER_DIR}/i2c.c
	${CC} ${CFLAGS} -c -o $@ $<

-include i2c_driver.d
