#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile is copied into the build directory
# and operated on from there.
#


MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit
ECHO_SERVER:=${SDDF}/examples/echo_server

SUPPORTED_BOARDS := odroidc4 odroidc2 maaxboard \
		    imx8mm_evk qemu_virt_aarch64 \
		    imx8mq_evk imx8mp_evk \
		    imx8mp_iotgate \
		    star64 qemu_virt_riscv64
TOOLCHAIN ?= clang
MICROKIT_CONFIG ?= debug
SYSTEM_FILE := echo_server.system
IMAGE_FILE := loader.img
REPORT_FILE := report.txt

include ${SDDF}/tools/make/board/common.mk

ECHO_SERVER := ${SDDF}/examples/echo_server
METAPROGRAM := $(ECHO_SERVER)/meta.py
LWIPDIR := network/ipstacks/lwip/src
BENCHMARK := $(SDDF)/benchmark
UTIL := $(SDDF)/util
ETHERNET_DRIVER := $(SDDF)/drivers/network/$(NET_DRIV_DIR)
ETHERNET_CONFIG_INCLUDE := ${ECHO_SERVER}/include/ethernet_config
SERIAL_COMPONENTS := $(SDDF)/serial/components
UART_DRIVER := $(SDDF)/drivers/serial/$(UART_DRIV_DIR)
TIMER_DRIVER := $(SDDF)/drivers/timer/$(TIMER_DRIV_DIR)
NETWORK_COMPONENTS := $(SDDF)/network/components

SDDF_CUSTOM_LIBC := 1

vpath %.c ${SDDF} ${ECHO_SERVER}

IMAGES := eth_driver.elf echo0.elf echo1.elf benchmark.elf idle.elf \
	  network_virt_rx.elf network_virt_tx.elf network_copy.elf \
	  network_copy0.elf network_copy1.elf timer_driver.elf \
	  serial_driver.elf serial_virt_tx.elf


CFLAGS += \
	  -Wno-unused-function \
	  -I$(BOARD_DIR)/include \
	  -I$(SDDF)/include/microkit \
	  -I$(SDDF)/include \
	  -I${ECHO_INCLUDE}/lwip \
	  -I${ETHERNET_CONFIG_INCLUDE} \
	  -I$(LWIPDIR)/include \
	  -I$(LWIPDIR)/include/ipv4 \
	  -I $(ECHO_SERVER)/include \
	  -MP


# Suppress warning from lwIP
CFLAGS += -Wno-tautological-constant-out-of-range-compare

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a \
	--end-group

ECHO_OBJS := echo.o utilization_socket.o \
	     udp_echo_socket.o tcp_echo_socket.o

DEPS := $(ECHO_OBJS:.o=.d)

all: loader.img

echo0.elf echo1.elf: $(ECHO_OBJS) libsddf_util.a lib_sddf_lwip_echo.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

network_copy0.elf network_copy1.elf: network_copy.elf
	cp $< $@

# Need to build libsddf_util_debug.a because it's included in LIBS
# for the unimplemented libc dependencies
${IMAGES}: libsddf_util_debug.a

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON)\
	    $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) \
	    --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .device_resources=ethernet_driver_device_resources.data eth_driver.elf
	$(OBJCOPY) --update-section .net_driver_config=net_driver.data eth_driver.elf
	$(OBJCOPY) --update-section .net_virt_rx_config=net_virt_rx.data network_virt_rx.elf
	$(OBJCOPY) --update-section .net_virt_tx_config=net_virt_tx.data network_virt_tx.elf
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client0_net_copier.data network_copy.elf network_copy0.elf
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client1_net_copier.data network_copy.elf network_copy1.elf
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client0.data echo0.elf
	$(OBJCOPY) --update-section .net_client_config=net_client_client0.data echo0.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client0.data echo0.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client1.data echo1.elf
	$(OBJCOPY) --update-section .net_client_config=net_client_client1.data echo1.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client1.data echo1.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_bench.data benchmark.elf
	$(OBJCOPY) --update-section .benchmark_config=benchmark_config.data benchmark.elf
	$(OBJCOPY) --update-section .benchmark_client_config=benchmark_client_config.data echo0.elf
	$(OBJCOPY) --update-section .benchmark_config=benchmark_idle_config.data idle.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client0.data echo0.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client1.data echo1.elf
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
		-netdev user,id=netdev0,hostfwd=tcp::1236-:1236,hostfwd=tcp::1237-:1237,hostfwd=udp::1235-:1235 \
		-global virtio-mmio.force-legacy=false \
		-d guest_errors

clean::
	${RM} -f *.elf .depend* $
	find . -name \*.[do] |xargs --no-run-if-empty rm

clobber:: clean
	rm -f ${IMAGE_FILE} ${REPORT_FILE}

-include $(DEPS)
