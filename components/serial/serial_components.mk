#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile snippet builds the serial RX and TX virtualisers
# it should be included into your project Makefile
#
# NOTES:
#  Generates serial_virt_rx.elf serial_virt_tx.elf
#

SERIAL_IMAGES:= serial_virt_rx.elf serial_virt_tx.elf
SERIAL_COMPONENT_OBJ := $(addprefix components/serial/, serial_virt_tx.o serial_virt_rx.o)

CFLAGS_serial := -I ${SDDF}/include

CHECK_SERIAL_FLAGS_MD5:=.serial_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_serial} | shasum | sed 's/ *-//')

${CHECK_SERIAL_FLAGS_MD5}:
	-rm -f .serial_cflags-*
	touch $@

${SERIAL_COMPONENT_OBJ}: |components/serial $(SDDF_LIBC_INCLUDE)
${SERIAL_COMPONENT_OBJ}: ${CHECK_SERIAL_FLAGS_MD5}

components/serial/serial_virt_%.o: ${SDDF}/components/serial/virt_%.c | $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} ${CFLAGS_serial} -o $@ -c $<

%.elf: components/serial/%.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

components/serial:
	mkdir -p $@

clean::
	rm -f serial_virt_[rt]x.[od] .serial_cflags-*

clobber::
	rm -f ${SERIAL_IMAGES}

-include components/serial/serial_virt_rx.d
-include components/serial/serial_virt_tx.d
