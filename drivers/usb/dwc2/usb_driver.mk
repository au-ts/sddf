#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build the DWC2 USB driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

USB_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

# TODO

usb:
	mkdir -p usb

clean::
	rm -rf usb

clobber::
	rm -f usb_driver.elf
