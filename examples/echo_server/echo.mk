#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit
SDDF_INCLUDE:=$(SDDF)/include/sddf
ECHO_SERVER:=${SDDF}/examples/echo_server
LWIPDIR:=network/ipstacks/lwip/src
BENCHMARK:=$(SDDF)/benchmark
UTIL:=$(SDDF)/util
ETHERNET_DRIVER:=$(SDDF)/drivers/network/$(DRIV_DIR)
ETHERNET_CONFIG_INCLUDE:=${ECHO_SERVER}/include/ethernet_config
TIMER_DRIVER:=$(SDDF)/drivers/clock/$(TIMER_DRV_DIR)
NETWORK_COMPONENTS:=$(SDDF)/network/components
NUM_NETWORK_CLIENTS:=-DNUM_NETWORK_CLIENTS=2

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SYSTEM_FILE := ${ECHO_SERVER}/board/$(MICROKIT_BOARD)/echo_server.system
IMAGE_FILE := loader.img
REPORT_FILE := report.txt

vpath %.c ${SDDF} ${ECHO_SERVER} ${NETWORK_COMPONENTS}

IMAGES := eth_driver.elf lwip.elf benchmark.elf idle.elf network_virt_rx.elf\
	  network_virt_tx.elf copy.elf timer_driver.elf

CFLAGS := -mcpu=$(CPU) \
	  -mstrict-align \
	  -ffreestanding \
	  -g3 -O3 -Wall \
	  -Wno-unused-function \
	  -DMICROKIT_CONFIG_$(MICROKIT_CONFIG) \
	  -I$(BOARD_DIR)/include \
	  -I$(SDDF)/include \
	  -I${ECHO_INCLUDE}/lwip \
	  -I${ETHERNET_CONFIG_INCLUDE} \
	  -I${SDDF}/$(LWIPDIR)/include \
	  -I${SDDF}/$(LWIPDIR)/include/ipv4 \
	  -MD \
	  -MP

LDFLAGS := -L$(BOARD_DIR)/lib -L${LIBC}
LIBS := --start-group -lmicrokit -Tmicrokit.ld -lc libsddf_util_debug.a --end-group

CHECK_FLAGS_BOARD_MD5:=.board_cflags-$(shell echo -- ${CFLAGS} ${BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//')

${CHECK_FLAGS_BOARD_MD5}:
	-rm -f .board_cflags-*
	touch $@

%.elf: %.o
	$(LD) $(LDFLAGS) $< $(LIBS) -o $@

include ${SDDF}/${LWIPDIR}/Filelists.mk

# NETIFFILES: Files implementing various generic network interface functions
# Override version in Filelists.mk
NETIFFILES:=$(LWIPDIR)/netif/ethernet.c

# LWIPFILES: All the above.
LWIPFILES=lwip.c $(COREFILES) $(CORE4FILES) $(NETIFFILES)
LWIP_OBJS := $(LWIPFILES:.c=.o) lwip.o utilization_socket.o \
	     udp_echo_socket.o

OBJS := $(LWIP_OBJS)
DEPS := $(filter %.d,$(OBJS:.o=.d))

all: loader.img

${LWIP_OBJS}: ${CHECK_FLAGS_BOARD_MD5}
lwip.elf: $(LWIP_OBJS) libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@
${LWIP_OBJS}: |${BUILD_DIR}/${LWIPDIR}
${BUILD_DIR}/${LWIPDIR}:
	mkdir -p $@/core/ipv4 $@/netif

# Need to build libsddf_util_debug.a because it's included in LIBS
# for the unimplemented libc dependencies
${IMAGES}: libsddf_util_debug.a

${IMAGE_FILE} $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)


include ${SDDF}/util/util.mk
include ${SDDF}/network/components/network_components.mk
include ${ETHERNET_DRIVER}/eth_driver.mk
include ${BENCHMARK}/benchmark.mk
include ${TIMER_DRIVER}/timer_driver.mk

clean::
	${RM} -f *.elf .depend* $
	find . -name \*.[do] |xargs --no-run-if-empty rm

clobber:: clean
	rm -f *.a
	rm -f ${IMAGE_FILE} ${REPORT_FILE}

-include $(DEPS)
