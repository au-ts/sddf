#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile snippet builds the network components
# (for example, simple RX and TX virtualisers)
# it should be included into your project Makefile
#
# NOTES:
# Generates network_virt_rx.elf network_virt_tx.elf network_arp.elf network_copy.elf network_vswitch.elf
# Requires ${SDDF}/util/util.mk to build the utility library for debug output

NETWORK_COMPONENTS_DIR := $(abspath $(dir $(lastword ${MAKEFILE_LIST})))
NETWORK_IMAGES:= network_virt_rx.elf network_virt_tx.elf network_arp.elf network_copy.elf network_vswitch.elf
components/network/%.o: ${SDDF}/components/network/%.c
	${CC} ${CFLAGS} -c -o $@ $<

NETWORK_COMPONENT_OBJ := $(addprefix components/network/, network_copy.o network_arp.o network_virt_tx.o network_virt_rx.o network_vswitch.o)

CHECK_NETWORK_FLAGS_MD5:=.network_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETWORK_FLAGS_MD5}:
	-rm -f .network_cflags-*
	touch $@

#vpath %.c ${SDDF}/components/network


${NETWORK_IMAGES}: LIBS := libsddf_util_debug.a ${LIBS}

${NETWORK_COMPONENT_OBJ}: |components/network $(SDDF_LIBC_INCLUDE)
${NETWORK_COMPONENT_OBJ}: ${CHECK_NETWORK_FLAGS_MD5}
${NETWORK_COMPONENT_OBJ}: CFLAGS+=${CFLAGS_network}

components/network/network_virt_%.o: ${SDDF}/components/network/virt_%.c
	${CC} ${CFLAGS} -c -o $@ $<

components/network/network_copy.o: ${SDDF}/components/network/copy.c
	${CC} ${CFLAGS} -c -o $@ $<

components/network/network_arp.o: ${SDDF}/components/network/arp.c
	${CC} ${CFLAGS} -c -o $@ $<

components/network/network_vswitch.o: ${SDDF}/components/network/vswitch.c
	${CC} ${CFLAGS} -c -o $@ $<

%.elf: components/network/%.o
	${LD} ${LDFLAGS} -o $@ $< ${LIBS}

clean::
	${RM} -f network_virt_[rt]x.[od] network_copy.[od] network_arp.[od] network_vswitch.[od]

clobber::
	${RM} -f ${NETWORK_IMAGES}
	rmdir components/network

components/network:
	mkdir -p $@

-include ${NETWORK_COMPONENTS_OBJS:.o=.d}
