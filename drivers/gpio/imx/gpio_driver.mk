#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the Meson gpio driver
#
# NOTES:
#  Generates gpio_driver.elf

GPIO_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

gpio_driver.elf: gpio/gpio_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

gpio/gpio_driver.o: ${GPIO_DRIVER_DIR}/gpio.c ${CHECK_FLAGS_BOARD_MD5} |gpio
	${CC} ${CFLAGS} -c -o $@ $<

gpio:
	mkdir -p gpio

clean::
	rm -rf gpio

clobber::
	rm -f gpio_driver.elf

# @ Tristan: so it recompiles if the config changes
-include gpio/gpio_driver.d