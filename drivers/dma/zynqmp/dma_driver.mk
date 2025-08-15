#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the zynqmp DMA driver.
# Assumes libsddf_util_debug.a is in ${LIBS}.

DMA_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

dma_driver.elf: dma/zynqmp/dma_driver.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

dma/zynqmp/dma_driver.o: ${DMA_DRIVER_DIR}/dma.c |dma/zynqmp
	$(CC) -c $(CFLAGS) -I${DMA_DRIVER_DIR}/include -o $@ $<

-include dma_driver.d

dma/zynqmp:
	mkdir -p $@

clean::
	rm -f dma/zynqmp/dma_driver.[do]

clobber::
	rm -rf dma
