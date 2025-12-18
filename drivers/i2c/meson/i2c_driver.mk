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
#  Has one parameter: I2C_BUS_NUM to select which bus is being driven

I2C_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

ifeq ($(PANCAKE_I2C),1)
i2c_driver.elf: i2c/i2c_pnk.o i2c/i2c_driver.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

I2C_PNK = ${UTIL}/util.pnk \
        ${SDDF}/include/microkit/os/sddf/i2c/queue.pnk \
        ${I2C_DRIVER_DIR}/i2c.pnk

i2c/i2c_pnk.S: $(I2C_PNK) |i2c
	cat $(I2C_PNK) | cpp -P | $(CAKE_COMPILER) --target=arm8 --pancake --main_return=true > $@

i2c/i2c_pnk.o: i2c/i2c_pnk.S
	$(CC) -c -mcpu=$(CPU) $< -o $@

i2c/i2c_driver.o: CFLAGS+=-I${I2C_DRIVER_DIR} -DI2C_BUS_NUM=${I2C_BUS_NUM} -DPANCAKE_I2C
i2c/i2c_driver.o: ${I2C_DRIVER_DIR}/i2c.c |i2c
	${CC} ${CFLAGS} -c -o $@ $<
else
i2c_driver.elf: i2c/i2c_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

i2c/i2c_driver.o: CFLAGS+=-I${I2C_DRIVER_DIR} -DI2C_BUS_NUM=${I2C_BUS_NUM}
i2c/i2c_driver.o: ${I2C_DRIVER_DIR}/i2c.c |i2c
	${CC} ${CFLAGS} -c -o $@ $<
endif

i2c:
	mkdir -p $@

clean::
	rm -rf i2c
	rm -f i2c/i2c_pnk.S i2c/i2c_pnk.o

clobber::
	rm -f i2c_driver.elf

-include i2c_driver.d
