#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

# @ivanv: Changes any of the params given e.g MICROKIT_CONFIG,
# doesn't actually cause a re-compile. We should fix this.

BUILD_DIR ?= build
MICROKIT_BOARD ?= imx8mm_evk
MICROKIT_CONFIG ?= debug
DRIV_DIR ?= imx
SYSTEM_FILE ?= echo_server_imx.system

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(TOOLCHAIN)),)
	TOOLCHAIN := aarch64-none-elf
endif

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	DRIV_DIR := meson
	SYSTEM_FILE := echo_server_meson.system
endif

CPU := cortex-a53

CC := $(TOOLCHAIN)-gcc
LD := $(TOOLCHAIN)-ld
AS := $(TOOLCHAIN)-as
MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

SDDF=$(abspath ../..)
SDDF_INCLUDE=$(SDDF)/include/sddf
LWIP=$(SDDF)/network/ipstacks/lwip/src
BENCHMARK=$(SDDF)/benchmark
UTIL=$(SDDF)/util
RING_BUFFER=$(SDDF)/network/libethsharedringbuffer
ETHERNET_DRIVER=$(SDDF)/drivers/network/$(DRIV_DIR)
TIMER_DRIVER=$(SDDF)/drivers/clock/$(DRIV_DIR)
NETWORK_COMPONENTS=$(SDDF)/network/components

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)

IMAGES := eth.elf lwip.elf benchmark.elf idle.elf mux_rx.elf mux_tx.elf copy.elf arp.elf timer.elf
CFLAGS := -mcpu=$(CPU) -mstrict-align -ffreestanding -g3 -O3 -Wall -Wno-unused-function

LDFLAGS := -L$(BOARD_DIR)/lib -L$(SDDF)/lib
LIBS := -lmicrokit -Tmicrokit.ld -lc

IMAGE_FILE = $(BUILD_DIR)/loader.img
REPORT_FILE = $(BUILD_DIR)/report.txt

CFLAGS += -I$(BOARD_DIR)/include \
	-I$(SDDF)/include \
	-Iinclude/lwip \
	-Iinclude/system_config \
	-I$(LWIP)/include \
	-I$(LWIP)/include/ipv4 \
	-MD \
	-MP

# COREFILES, CORE4FILES: The minimum set of files needed for lwIP.
COREFILES=$(LWIP)/core/init.c \
	$(LWIP)/core/def.c \
	$(LWIP)/core/dns.c \
	$(LWIP)/core/inet_chksum.c \
	$(LWIP)/core/ip.c \
	$(LWIP)/core/mem.c \
	$(LWIP)/core/memp.c \
	$(LWIP)/core/netif.c \
	$(LWIP)/core/pbuf.c \
	$(LWIP)/core/raw.c \
	$(LWIP)/core/stats.c \
	$(LWIP)/core/sys.c \
	$(LWIP)/core/altcp.c \
	$(LWIP)/core/altcp_alloc.c \
	$(LWIP)/core/altcp_tcp.c \
	$(LWIP)/core/tcp.c \
	$(LWIP)/core/tcp_in.c \
	$(LWIP)/core/tcp_out.c \
	$(LWIP)/core/timeouts.c \
	$(LWIP)/core/udp.c

CORE4FILES=$(LWIP)/core/ipv4/autoip.c \
	$(LWIP)/core/ipv4/dhcp.c \
	$(LWIP)/core/ipv4/etharp.c \
	$(LWIP)/core/ipv4/icmp.c \
	$(LWIP)/core/ipv4/igmp.c \
	$(LWIP)/core/ipv4/ip4_frag.c \
	$(LWIP)/core/ipv4/ip4.c \
	$(LWIP)/core/ipv4/ip4_addr.c

# NETIFFILES: Files implementing various generic network interface functions
NETIFFILES=$(LWIP)/netif/ethernet.c

# LWIPFILES: All the above.
LWIPFILES=lwip.c $(COREFILES) $(CORE4FILES) $(NETIFFILES)
LWIP_OBJS := $(LWIPFILES:.c=.o) lwip.o sddf_network_sharedringbuffer.o utilization_socket.o udp_echo_socket.o sddf_timer_client.o printf.o putchar_serial.o

ETH_OBJS := $(ETHERNET_DRIVER)/ethernet.o sddf_network_sharedringbuffer.o printf.o putchar_debug.o
MUX_RX_OBJS := $(NETWORK_COMPONENTS)/mux_rx.o sddf_network_sharedringbuffer.o printf.o putchar_debug.o
MUX_TX_OBJS := $(NETWORK_COMPONENTS)/mux_tx.o sddf_network_sharedringbuffer.o $(UTIL)/cache.o printf.o putchar_debug.o
COPY_OBJS := $(NETWORK_COMPONENTS)/copy.o sddf_network_sharedringbuffer.o printf.o putchar_debug.o
BENCH_OBJS := $(BENCHMARK)/benchmark.o printf.o putchar_serial.o
IDLE_OBJS := $(BENCHMARK)/idle.o printf.o putchar_debug.o
ARP_OBJS := $(NETWORK_COMPONENTS)/arp.o sddf_network_sharedringbuffer.o printf.o putchar_serial.o
TIMER_OBJS := $(TIMER_DRIVER)/timer.o printf.o putchar_debug.o

OBJS := $(sort $(addprefix $(BUILD_DIR)/, $(ETH_OBJS) $(MUX_RX_OBJS) $(MUX_TX_OBJS)\
	$(COPY_OBJS) $(BENCH_OBJS) $(IDLE_OBJS) \
	$(LWIP_OBJS) $(ARP_OBJS) $(TIMER_OBJS)))
DEPS := $(OBJS:.o=.d)

all: $(IMAGE_FILE)
-include $(DEPS)

$(BUILD_DIR)/%.d $(BUILD_DIR)/%.o: %.c Makefile
	mkdir -p `dirname $(BUILD_DIR)/$*.o`
	$(CC) -c $(CFLAGS) $< -o $(BUILD_DIR)/$*.o

$(BUILD_DIR)/%.o: %.s Makefile
	$(AS) -g3 -mcpu=$(CPU) $< -o $@

$(BUILD_DIR)/printf.o: $(UTIL)/printf.c $(SDDF_INCLUDE)/util/printf.h
	$(CC) -c $(CFLAGS) $(UTIL)/printf.c -o $(BUILD_DIR)/printf.o

$(BUILD_DIR)/putchar_debug.o: $(UTIL)/putchar_debug.c
	$(CC) -c $(CFLAGS) $(UTIL)/putchar_debug.c -o $(BUILD_DIR)/putchar_debug.o

$(BUILD_DIR)/putchar_serial.o: $(UTIL)/putchar_serial.c
	$(CC) -c $(CFLAGS) $(UTIL)/putchar_serial.c -o $(BUILD_DIR)/putchar_serial.o

$(BUILD_DIR)/sddf_timer_client.o: FORCE
	BUILD_DIR=$(abspath $(BUILD_DIR)) MICROKIT_INCLUDE=$(BOARD_DIR)/include make -C $(SDDF)/timer/client

$(BUILD_DIR)/sddf_network_sharedringbuffer.o: FORCE
	BUILD_DIR=$(abspath $(BUILD_DIR)) MICROKIT_INCLUDE=$(BOARD_DIR)/include make -C $(RING_BUFFER)

$(BUILD_DIR)/eth.elf: $(addprefix $(BUILD_DIR)/, $(ETH_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/lwip.elf: $(addprefix $(BUILD_DIR)/, $(LWIP_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/mux_rx.elf: $(addprefix $(BUILD_DIR)/, $(MUX_RX_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/mux_tx.elf: $(addprefix $(BUILD_DIR)/, $(MUX_TX_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/copy.elf: $(addprefix $(BUILD_DIR)/, $(COPY_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/benchmark.elf: $(addprefix $(BUILD_DIR)/, $(BENCH_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/idle.elf: $(addprefix $(BUILD_DIR)/, $(IDLE_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/arp.elf: $(addprefix $(BUILD_DIR)/, $(ARP_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(BUILD_DIR)/timer.elf: $(addprefix $(BUILD_DIR)/, $(TIMER_OBJS))
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(IMAGE_FILE) $(REPORT_FILE): $(addprefix $(BUILD_DIR)/, $(IMAGES)) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)

.PHONY: all compile clean

%.o:
	$(CC) $(CFLAGS) -c $(@:.o=.c) -o $@

clean:
	rm -f *.o *.elf .depend*
	find . -name \*.o |xargs --no-run-if-empty rm

FORCE: ;