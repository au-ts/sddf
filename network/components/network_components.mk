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
# Generates network_virt_rx.elf network_virt_tx.elf network_arp.elf network_copy.elf
# Requires ${SDDF}/util/util.mk to build the utility library for debug output

NETWORK_COMPONENTS_DIR := $(abspath $(dir $(lastword ${MAKEFILE_LIST})))
NETWORK_IMAGES:= network_virt_rx.elf network_virt_tx.elf network_arp.elf network_copy.elf
network/components/%.o: ${SDDF}/network/components/%.c
	${CC} ${CFLAGS} -c -o $@ $<

NETWORK_COMPONENT_OBJ := $(addprefix network/components/, network_copy.o network_arp.o network_virt_tx.o network_virt_rx.o)

CHECK_NETWORK_FLAGS_MD5:=.network_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETWORK_FLAGS_MD5}:
	-rm -f .network_cflags-*
	touch $@

#vpath %.c ${SDDF}/network/components


${NETWORK_IMAGES}: LIBS := libsddf_util_debug.a ${LIBS}

${NETWORK_COMPONENT_OBJ}: |network/components
${NETWORK_COMPONENT_OBJ}: ${CHECK_NETWORK_FLAGS_MD5}
${NETWORK_COMPONENT_OBJ}: CFLAGS+=${CFLAGS_network}

network/components/network_virt_%.o: ${SDDF}/network/components/virt_%.c
	${CC} ${CFLAGS} -c -o $@ $<

network/components/network_copy.o: ${SDDF}/network/components/copy.c
	${CC} ${CFLAGS} -c -o $@ $<

network/components/network_arp.o: ${SDDF}/network/components/arp.c
	${CC} ${CFLAGS} -c -o $@ $<

%.elf: network/components/%.o
	${LD} ${LDFLAGS} -o $@ $< ${LIBS}

clean::
	${RM} -f network_virt_[rt]x.[od] network_copy.[od] network_arp.[od]

clobber::
	${RM} -f ${NETWORK_IMAGES}
	rmdir network/components

network/components:
	mkdir -p $@

-include ${NETWORK_COMPONENTS_OBJS:.o=.d}
