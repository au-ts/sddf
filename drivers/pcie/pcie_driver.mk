#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build PCIe driver
#

PCIE_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
CHECK_PCIEDRV_FLAGS_MD5:=.pciedrv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_pcie} | shasum | sed 's/ *-//')

${CHECK_PCIEDRV_FLAGS_MD5}:
	-rm -f .pcie_cflags-*
	touch $@

pcie_driver.elf: pcie/pcie.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

pcie/pcie.o: ${PCIE_DRIVER_DIR}/pcie.c ${CHECK_PCIEDRV_FLAGS_MD5} | $(SDDF_LIBC_INCLUDE)
	mkdir -p pcie
	${CC} -c ${CFLAGS} ${CFLAGS_pcie} -I ${PCIE_DRIVER_DIR} -o $@ $<


-include pcie.d
