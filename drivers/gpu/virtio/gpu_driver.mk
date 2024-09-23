#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the VirtIO driver
#
# NOTES:
#   Generates gpu_driver.elf
#   Needs the appropriate VirtIO-MMIO region to be set in System Description File.
# 	This can be dependent on how many VirtIO MMIO devices exist within your system.
#   Assumes libsddf_util_debug.a is in LIBS

GPU_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

CFLAGS_gpu ?=

CHECK_GPU_DRV_FLAGS_MD5:=.gpu_drv_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_gpu} | shasum | sed 's/ *-//')

${CHECK_GPU_DRV_FLAGS_MD5}:
	-rm -f .gpu_drv_cflags-*
	touch $@

gpu_driver.elf: gpu/virtio/gpu_driver.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

gpu/virtio/gpu_driver.o: ${GPU_DRIVER_DIR}gpu.c ${CHECK_GPU_DRV_FLAGS_MD5}
	mkdir -p gpu/virtio
	${CC} -c ${CFLAGS} ${CFLAGS_gpu} -I ${GPU_DRIVER_DIR} -o $@ $<

-include virtio/gpu.d

clean::
	rm -f gpu/virtio/gpu_driver.[do]
clobber:: clean
	rm -rf gpu_driver.elf gpu
