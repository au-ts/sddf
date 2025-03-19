#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the IMX8 can driver
#
# NOTES:
#  Generates can_driver.elf
#  Expects libsddf_util_debug.a to be in ${LIBS}
CAN_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

can_driver.elf: can/can.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

can/can.o: ${CAN_DIR}/can.c ${CHECK_FLAGS_BOARD_MD5} |can
	${CC} ${CFLAGS} -o $@ -c $<

can:
	mkdir -p can

clean::
	rm -rf can
clobber::
	rm -f can_driver.elf