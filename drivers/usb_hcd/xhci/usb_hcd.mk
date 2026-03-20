#
# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build the xHCI driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

USB_HCD_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

CHECK_XHCI_FLAGS_MD5:=.xhci_cflags-$(shell echo -- ${CFLAGS} | shasum | sed 's/ *-//')

${CHECK_XHCI_FLAGS_MD5}:
	-rm -f .xhci_cflags-*
	touch $@

usb_hcd.elf: usb_hcd.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

usb_hcd.o: ${USB_HCD_DIR}/xhci.c ${CHECK_XHCI_FLAGS_MD5}
	$(CC) -c $(CFLAGS) -I${USB_HCD_DIR} -o $@ $<

QEMU_USB_HCD_ARGS := -device qemu-xhci,addr=0x5.0,id=xhci

-include usb_hcd.d

clean::
	rm -f usb_hcd.o

clobber::
	rm -f usb_hcd.elf
