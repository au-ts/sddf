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

NETWORK_IMAGES:= network_virt_rx.elf network_virt_tx.elf arp.elf copy.elf

CFLAGS_network := ${NUM_NETWORK_CLIENTS}

CHECK_NETWORK_FLAGS_MD5:=.network_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_network} | md5sum | sed 's/  *-//')

${CHECK_NETWORK_FLAGS_MD5}:
	-rm -f .network_cflags-*
	touch $@
VPATH += :${SDDF}/network/components

network_virt_%.elf: network_virt_%.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@ libsddf_util_debug.a

copy.elf arp.elf: LIBS := libsddf_util_debug.a ${LIBS}

%.elf: %.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

arp.o copy.o network_virt_tx.o network_virt_rx.o: ${CHECK_NETWORK_FLAGS_MD5}
network_virt_%.o: ${SDDF}/network/components/virt_%.c 
	${CC} ${CFLAGS} ${CFLAGS_network} -o $@ -MF .${@:.o=.d} -c $<

arp.o copy.o: CFLAGS+=${CFLAGS_network}

clean::
	rm -f network_virt_[rt]x.[od] copy.[od] arp.[od]

clobber::
	rm -f ${IMAGES}

-include network_virt_rx.d
-include network_virt_tx.d
-include arp.d
-include copy.d
