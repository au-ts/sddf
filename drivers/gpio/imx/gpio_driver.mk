#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX gpio driver
#
# NOTES
#  Generates gpio_driver.elf
#  Needs five variables set in system description file:
#  gpio1_regs --- the GPIO1 instance registers.
#  gpio2_regs --- the GPIO2 instance registers.
#  gpio3_regs --- the GPIO3 instance registers.
#  gpio4_regs --- the GPIO4 instance registers.
#  gpio5_regs --- the GPIO5 instance registers.
#  Needs a config file to be defined that defines what channels are used
#  May need to change the offsets used depending on the page start of the above three variables


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

-include gpio/gpio_driver.d
