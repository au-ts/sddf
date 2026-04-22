#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the PCI driver
#
# NOTES:
#  Generates pci_driver.elf
#  Expects libsddf_util_debug.a to be in ${LIBS}

PCI_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

pci_driver.elf: pci/pci.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

pci/pci.o: ${PCI_DIR}/pci.c ${CHECK_FLAGS_BOARD_MD5} |pci $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -o $@ -c $<

pci:
	mkdir -p pci

clean::
	rm -rf pci
clobber::
	rm -f pci_driver.elf
