#
# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build the PWM driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

PWM_DRIVER_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

CHECK_PWM_FLAGS_MD5:=.nvme_cflags-$(shell echo -- ${CFLAGS} | shasum | sed 's/ *-//')

${CHECK_PWM_FLAGS_MD5}:
	-rm -f .pwm_cflags-*
	touch $@

pwm_driver.elf: pwm_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

pwm_driver.o: ${PWM_DRIVER_DIR}/pwm.c ${CHECK_PWM_FLAGS_MD5}
	$(CC) -c $(CFLAGS) -I${PWM_DRIVER_DIR} -o $@ $<

-include pwm_driver.d

clean::
	rm -f pwm_driver.o

clobber::
	rm -f pwm_driver.elf
