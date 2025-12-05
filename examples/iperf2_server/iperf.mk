#
# Copyright 2025, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile is copied into the build directory
# and operated on from there.
#

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit
IPERF2_SERVER:=${SDDF}/examples/iperf2_server

SUPPORTED_BOARDS := odroidc4 odroidc2 maaxboard \
		    imx8mm_evk qemu_virt_aarch64 \
		    imx8mq_evk imx8mp_evk \
		    imx8mp_iotgate \
		    star64 qemu_virt_riscv64
TOOLCHAIN ?= clang
MICROKIT_CONFIG ?= debug
SYSTEM_FILE := iperf2_server.system
IMAGE_FILE := loader.img
REPORT_FILE := report.txt

include ${SDDF}/tools/make/board/common.mk

IPERF2_SERVER := ${SDDF}/examples/iperf2_server
METAPROGRAM := $(IPERF2_SERVER)/meta.py
LWIPDIR := network/ipstacks/lwip/src
BENCHMARK := $(SDDF)/benchmark
UTIL := $(SDDF)/util
ETHERNET_DRIVER := $(SDDF)/drivers/network/$(NET_DRIV_DIR)
ETHERNET_CONFIG_INCLUDE := ${IPERF2_SERVER}/include/ethernet_config
SERIAL_COMPONENTS := $(SDDF)/serial/components
UART_DRIVER := $(SDDF)/drivers/serial/$(UART_DRIV_DIR)
TIMER_DRIVER := $(SDDF)/drivers/timer/$(TIMER_DRIV_DIR)
NETWORK_COMPONENTS := $(SDDF)/network/components

SDDF_CUSTOM_LIBC := 1

vpath %.c ${SDDF} ${IPERF2_SERVER}

IMAGES := eth_driver.elf iperf2.elf benchmark.elf idle.elf \
	  network_virt_rx.elf network_virt_tx.elf network_copy.elf \
	  timer_driver.elf serial_driver.elf serial_virt_tx.elf


CFLAGS += \
	  -Wno-unused-function \
	  -I$(BOARD_DIR)/include \
	  -I$(SDDF)/include/microkit \
	  -I$(SDDF)/include \
	  -I${IPERF2_INCLUDE}/lwip \
	  -I${ETHERNET_CONFIG_INCLUDE} \
	  -I$(LWIPDIR)/include \
	  -I$(LWIPDIR)/include/ipv4 \
	  -I$(LWIPDIR)/include/apps/lwiperf \
	  -I $(IPERF2_SERVER)/include \
	  -MP


# Suppress warning from lwIP
CFLAGS += -Wno-tautological-constant-out-of-range-compare

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a \
	--end-group

IPERF2_OBJS := iperf2.o iperf2_tcp.o

DEPS := $(IPERF2_OBJS:.o=.d)

all: loader.img

iperf2.elf: $(IPERF2_OBJS) libsddf_util.a lib_sddf_lwip_echo.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# Need to build libsddf_util_debug.a because it's included in LIBS
# for the unimplemented libc dependencies
${IMAGES}: libsddf_util_debug.a

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON)\
	    $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) \
	    --dtb $(DTB) --output . --sdf $(SYSTEM_FILE) --objcopy $(OBJCOPY)
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .device_resources=ethernet_driver_device_resources.data eth_driver.elf
	$(OBJCOPY) --update-section .net_driver_config=net_driver.data eth_driver.elf
	$(OBJCOPY) --update-section .net_virt_rx_config=net_virt_rx.data network_virt_rx.elf
	$(OBJCOPY) --update-section .net_virt_tx_config=net_virt_tx.data network_virt_tx.elf
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client0_net_copier.data network_copy.elf network_copy0.elf
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client0.data iperf20.elf
	$(OBJCOPY) --update-section .net_client_config=net_client_client0.data iperf20.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client0.data iperf20.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client0.data iperf20.elf
	touch $@

${IMAGE_FILE} $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) \
	--board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) \
	-o $(IMAGE_FILE) -r $(REPORT_FILE)


include ${SDDF}/util/util.mk
include ${SDDF}/network/components/network_components.mk
include ${SDDF}/network/lib_sddf_lwip/lib_sddf_lwip.mk
include ${ETHERNET_DRIVER}/eth_driver.mk
include ${BENCHMARK}/benchmark.mk
include ${TIMER_DRIVER}/timer_driver.mk
include ${UART_DRIVER}/serial_driver.mk
include ${SERIAL_COMPONENTS}/serial_components.mk

qemu: $(IMAGE_FILE)
	$(QEMU) $(QEMU_ARCH_ARGS) \
		-nographic \
		-device virtio-net-device,netdev=netdev0 \
		-netdev user,id=netdev0,\
hostfwd=udp::1235-10.0.2.15:1235,\
hostfwd=tcp::1236-10.0.2.15:1236,\
hostfwd=tcp::1237-10.0.2.15:1237,\
hostfwd=udp::1238-10.0.2.16:1235,\
hostfwd=tcp::1239-10.0.2.16:1236,\
hostfwd=tcp::1240-10.0.2.16:1237 \
		-global virtio-mmio.force-legacy=false \
		-d guest_errors -smp 4

clean::
	${RM} -f *.elf .depend* $
	find . -name \*.[do] |xargs --no-run-if-empty rm

clobber:: clean
	rm -f ${IMAGE_FILE} ${REPORT_FILE}

-include $(DEPS)
