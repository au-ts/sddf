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
TIMER_DRIVER:=$(SDDF)/drivers/clock/$(DRIV_DIR)
TIMER_CLIENT:=${SDDF}/timer/client
NETWORK_COMPONENTS:=$(SDDF)/network/components
NUM_NETWORK_CLIENTS:=-DNUM_NETWORK_CLIENTS=3

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
SYSTEM_FILE := ${ECHO_SERVER}/board/$(MICROKIT_BOARD)/echo_server.system
IMAGE_FILE := loader.img
REPORT_FILE := report.txt

vpath %.c ${SDDF} ${ECHO_SERVER} ${NETWORK_COMPONENTS}

IMAGES := eth.elf lwip.elf benchmark.elf idle.elf network_virt_rx.elf\
	  network_virt_tx.elf copy.elf timer.elf

CFLAGS := -mcpu=$(CPU) \
	  -mstrict-align \
	  -ffreestanding \
	  -g3 -O3 -Wall \
	  -Wno-unused-function \
	  -DMICROKIT_CONFIG_$(MICROKIT_CONFIG) \
	  -I$(BOARD_DIR)/include \
	  -I$(SDDF)/include \
	  -I${ECHO_INCLUDE}/lwip \
	  -I${ECHO_INCLUDE}/ethernet_config \
	  -I${SDDF}/$(LWIPDIR)/include \
	  -I${SDDF}/$(LWIPDIR)/include/ipv4 \
	  -MD \
	  -MP

LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib -L${LIBC}
LIBS := -lmicrokit -Tmicrokit.ld -lc

include ${SDDF}/${LWIPDIR}/Filelists.mk

# NETIFFILES: Files implementing various generic network interface functions
# OVerride version in Filelists.mk
NETIFFILES:=$(LWIPDIR)/netif/ethernet.c

# LWIPDIRFILES: All the above.
LWIPFILES=lwip.c $(COREFILES) $(CORE4FILES) $(NETIFFILES)
LWIP_OBJS := $(LWIPFILES:.c=.o) lwip.o utilization_socket.o \
	     udp_echo_socket.o libtimerclient.a libsddf_util.a

BENCH_OBJS := $(BENCHMARK)/benchmark.o libsddf_util.a
IDLE_OBJS := $(BENCHMARK)/idle.o libsddf_util_debug.a
TIMER_OBJS := $(TIMER_DRIVER)/timer.o libsddf_util_debug.a

OBJS := $(sort $(addprefix $(BUILD_DIR)/, $(ETH_OBJS) \
	$(BENCH_OBJS) $(IDLE_OBJS) \
	$(ARP_OBJS) $(TIMER_OBJS)))
DEPS := $(filter %.d,$(OBJS:.o=.d))

all: loader.img

-include $(DEPS)


lwip.elf: $(LWIP_OBJS)
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

${LWIP_OBJS}: |${BUILD_DIR}/${LWIPDIR}

${BUILD_DIR}/${LWIPDIR}:
	mkdir -p $@/core/ipv4 $@/netif

benchmark.elf: $(BENCH_OBJS)
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

idle.elf: $(IDLE_OBJS)
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

timer.elf: $(TIMER_OBJS)
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

${IMAGE_FILE} $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)


include ${SDDF}/util/util.mk
include ${SDDF}/network/components/network_components.mk
include ${ETHERNET_DRIVER}/ethdriver.mk
include ${TIMER_CLIENT}/timerclient.mk


clean::
	rm -f *.o *.elf .depend*
	find . -name \*.o |xargs --no-run-if-empty rm

clobber:: clean
	rm -f ${IMAGE_FILE} ${REPORT_FILE}

