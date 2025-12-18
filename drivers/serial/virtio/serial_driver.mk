#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the virtio console driver.
#
# NOTES:
#   Builds serial_driver.elf

SERIAL_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
SERIAL_QUEUE_INCLUDE := ${SDDF}/include/sddf/serial

ifeq ($(PANCAKE_SERIAL_DRIVER),1)
DRIVER_PNK = ${UTIL}/util.pnk \
	${SERIAL_QUEUE_INCLUDE}/queue.pnk \
	${SERIAL_DRIVER_DIR}/console.pnk

CC_IS_CLANG := $(shell $(CC) --version 2>/dev/null | grep -q clang && echo yes || echo no)

ifeq ($(CC_IS_CLANG),yes)
    TARGET_FLAG := -target aarch64-none-elf
else
    TARGET_FLAG :=
endif

serial_pnk.o: serial_pnk.S
	$(CC) -c -mcpu=$(CPU) $(TARGET_FLAG) $< -o $@

serial_pnk.S: $(DRIVER_PNK)
	cat $(DRIVER_PNK) | cpp -P | $(CAKE_COMPILER) --target=arm8 --pancake --main_return=true > $@

serial_driver.elf: serial_pnk.o serial/virtio/serial_driver.o pancake_ffi.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/virtio/serial_driver.o: ${SERIAL_DRIVER_DIR}/console.c |serial/virtio
	$(CC) -c $(CFLAGS) -DPANCAKE_SERIAL -I${SERIAL_DRIVER_DIR}/include -o $@ $<

else
serial_driver.elf: serial/virtio/serial_driver.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/virtio/serial_driver.o: ${SERIAL_DRIVER_DIR}/console.c |serial/virtio
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -o $@ $<
endif

serial/virtio:
	mkdir -p $@

-include serial/virtio/serial_driver.d

clean::
	rm -f serial/virtio/serial_driver.[do]

clobber::
	rm -rf serial
