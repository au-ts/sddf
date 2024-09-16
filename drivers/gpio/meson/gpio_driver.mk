#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson gpio driver
#
# NOTES
#  Generates gpio_driver.elf
#  Needs three variables set in system description file:
#  gpio --- the GPIO registers.
#  gpio_ao --- the Always On GPIO registers.
#  interupt_control -- the interrupt control registers.
#  Needs a config file to be defined that defines what channels are used

GPIO_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

gpio_driver.elf: gpio/gpio_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

gpio/gpio_driver.o: CFLAGS+=-I${GPIO_DRIVER_DIR}
gpio/gpio_driver.o: ${GPIO_DRIVER_DIR}/gpio.c |gpio
	${CC} ${CFLAGS} -c -o $@ $<

gpio:
	mkdir -p $@

clean::
	rm -rf gpio

clobber::
	rm -f gpio_driver.elf

-include gpio_driver.d
