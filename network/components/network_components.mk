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
# Generates network_virt_rx.elf network_virt_tx.elf arp.elf copy.elf
# Relies on the variable NUM_NETWORK_CLIENTS to be a flag for
# the C compiler to configure the virtualisers
# Requires ${SDDF}/util/util.mk to build the utility library for debug output

ifeq ($(strip $(NUM_NETWORK_CLIENTS)),)
$(error Specify the number of clients for the network virtualisers.  Expect -DNUM_NETWORK_CLIENTS=3 or similar)
endif


NETWORK_COMPONENTS_DIR := $(abspath $(dir $(lastword ${MAKEFILE_LIST})))
NETWORK_IMAGES:= network_virt_rx.elf network_virt_tx.elf arp.elf copy.elf
network/components/%.o: ${SDDF}/network/components/%.c
	${CC} ${CFLAGS} -c -o $@ $<

NETWORK_COMPONENT_OBJ := $(addprefix network/components/, copy.o arp.o network_virt_tx.o network_virt_rx.o)

CFLAGS_network += ${NUM_NETWORK_CLIENTS}

CHECK_NETWORK_FLAGS_MD5:=.network_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | shasum | sed 's/ *-//')

${CHECK_NETWORK_FLAGS_MD5}:
	-rm -f .network_cflags-*
	touch $@

#vpath %.c ${SDDF}/network/components


${NETWORK_IMAGES): LIBS := libsddf_util_debug.a ${LIBS}

${NETWORK_COMPONENT_OBJ}: |network/components
${NETWORK_COMPONENT_OBJ}: ${CHECK_NETWORK_FLAGS_MD5}
${NETWORK_COMPONENT_OBJ}: CFLAGS+=${CFLAGS_network}

network/components/network_virt_%.o: ${SDDF}/network/components/virt_%.c 
	${CC} ${CFLAGS} -c -o $@ $<

%.elf: network/components/%.o
	${LD} ${LDFLAGS} -o $@ $< ${LIBS}

clean::
	rm -f network_virt_[rt]x.[od] copy.[od] arp.[od]

clobber::
	rm -f ${IMAGES}

network/components:
	mkdir -p $@

-include ${NETWORK_COMPONENTS_OBJS:.o=.d}
