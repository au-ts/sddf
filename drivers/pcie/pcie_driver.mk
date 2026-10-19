#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the PCIe driver
#
# NOTES:
#  Generates pcie_driver.elf
#  Expects libsddf_util_debug.a to be in ${LIBS}

PCI_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

pcie_driver.elf: pcie/pcie.o pcie/ecam.o pcie/bus_scan.o pcie/arbiter.o pcie/debug.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

pcie/%.o: ${PCI_DIR}/%.c ${CHECK_FLAGS_BOARD_MD5} |pcie $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -o $@ -c $<

pcie:
	mkdir -p pcie

clean::
	rm -rf pcie
clobber::
	rm -f pcie_driver.elf
