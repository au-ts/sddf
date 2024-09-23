#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile snippet builds the gpu virtualiser
# it should be included into your project Makefile
#
# NOTES:
#  Generates gpu_virt.elf
#

CFLAGS_gpu ?=

CHECK_GPU_VIRT_FLAGS_MD5:=.gpu_virt_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_gpu} | shasum | sed 's/ *-//')

${CHECK_GPU_VIRT_FLAGS_MD5}:
	-rm -f .gpu_virt_cflags-*
	touch $@

gpu_virt.elf: gpu_virt.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

gpu_virt.o: ${SDDF}/gpu/components/virt.c ${CHECK_GPU_VIRT_FLAGS_MD5}
	${CC} ${CFLAGS} ${CFLAGS_gpu} -o $@ -c $<

-include gpu_virt.d

clean::
	rm -f gpu_virt.[od] .gpu_virt_cflags-*
clobber:: clean
	rm -f gpu_virt.elf
