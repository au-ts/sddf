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
#  Requires libsddf_util_debug.a in ${LIBS}

# Change this after clk driver is integrated

#  Needs two variables set in system description file:
#  i2c_bus --- the i2c controller
#  clk --- the clock registers

I2C_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

i2c_driver.elf: i2c/i2c_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

i2c/i2c_driver.o: CFLAGS+=-I${I2C_DRIVER_DIR} 
i2c/i2c_driver.o: ${I2C_DRIVER_DIR}/i2c.c |i2c
	${CC} ${CFLAGS} -c -o $@ $<

i2c:
	mkdir -p $@

clean::
	rm -rf i2c

clobber::
	rm -f i2c_driver.elf

-include i2c_driver.d
