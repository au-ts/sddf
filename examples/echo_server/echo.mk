#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

QEMU := qemu-system-aarch64
DTC := dtc
PYTHON ?= python3

METAPROGRAM := $(TOP)/meta.py

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit
ECHO_SERVER:=${SDDF}/examples/echo_server
LWIPDIR:=network/ipstacks/lwip/src
BENCHMARK:=$(SDDF)/benchmark
UTIL:=$(SDDF)/util
ETHERNET_DRIVER:=$(SDDF)/drivers/network/$(DRIV_DIR)
SERIAL_COMPONENTS := $(SDDF)/serial/components
SERIAL_DRIVER := $(SDDF)/drivers/serial/$(SERIAL_DRIV_DIR)
TIMER_DRIVER:=$(SDDF)/drivers/timer/$(TIMER_DRV_DIR)
NETWORK_COMPONENTS:=$(SDDF)/network/components

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
IMAGE_FILE := loader.img
REPORT_FILE := report.txt
SYSTEM_FILE := echo_server.system
DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb
METAPROGRAM := $(TOP)/meta.py

vpath %.c ${SDDF} ${ECHO_SERVER}

IMAGES := eth_driver.elf benchmark.elf idle.elf network_virt_rx.elf\
	  network_virt_tx.elf timer_driver.elf ip_collector.elf\
	  serial_driver.elf serial_virt_tx.elf

NUMBERS := $(shell seq 0 $$(( $(NUM_CLIENTS) - 1 )) )
ECHO_IMAGES := $(addsuffix .elf,$(addprefix echo,${NUMBERS}))
NET_COPY_IMAGES := $(addsuffix .elf,$(addprefix network_copy,${NUMBERS}))

CFLAGS := -mcpu=$(CPU) \
	  -mstrict-align \
	  -ffreestanding \
	  -g3 -O3 -Wall \
	  -Wno-unused-function \
	  -DMICROKIT_CONFIG_$(MICROKIT_CONFIG) \
	  -I$(BOARD_DIR)/include \
	  -I$(SDDF)/include/microkit \
	  -I$(SDDF)/include \
	  -I${ECHO_INCLUDE}/lwip \
	  -I${SDDF}/$(LWIPDIR)/include \
	  -I${SDDF}/$(LWIPDIR)/include/ipv4 \
	  -MD \
	  -MP

LDFLAGS := -L$(BOARD_DIR)/lib -L${LIBC}
LIBS := --start-group -lmicrokit -Tmicrokit.ld -lc libsddf_util_debug.a --end-group

CHECK_FLAGS_BOARD_MD5 := .board_cflags-$(shell echo -- ${CFLAGS} ${BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//')

${CHECK_FLAGS_BOARD_MD5}:
	-rm -f .board_cflags-*
	touch $@

%.elf: %.o libsddf_util.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

ECHO_OBJS := echo.o utilization_socket.o \
	     udp_echo_socket.o tcp_echo_socket.o

DEPS := $(ECHO_OBJS:.o=.d)

all: loader.img

${ECHO_OBJS}: ${CHECK_FLAGS_BOARD_MD5}
echo%.elf: $(ECHO_OBJS) libsddf_util.a lib_sddf_lwip_echo.a |$(SYSTEM_FILE)
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client$*.data echo$*.elf
	$(OBJCOPY) --update-section .net_client_config=net_client_client$*.data echo$*.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client$*.data echo$*.elf
	$(OBJCOPY) --update-section .client_config=client_config_$*.data echo$*.elf
	if [ $* -eq 0 ]; then \
		$(OBJCOPY) --update-section .benchmark_client_config=benchmark_client_config.data echo$*.elf; \
		$(OBJCOPY) --update-section .serial_client_config=serial_client_client$*.data echo$*.elf; \
	fi

network_copy%.elf: network_copy.elf |$(SYSTEM_FILE)
	cp $< $@
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client$*_net_copier.data network_copy$*.elf

# Need to build libsddf_util_debug.a because it's included in LIBS
# for the unimplemented libc dependencies
${IMAGES}: libsddf_util_debug.a

$(DTB): $(DTS)
	dtc -q -I dts -O dtb $(DTS) > $(DTB)

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE) --num-clients $(NUM_CLIENTS) --target-client $(TARGET_CLIENT)
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .device_resources=ethernet_driver_device_resources.data eth_driver.elf
	$(OBJCOPY) --update-section .net_driver_config=net_driver.data eth_driver.elf
	$(OBJCOPY) --update-section .net_virt_rx_config=net_virt_rx.data network_virt_rx.elf
	$(OBJCOPY) --update-section .net_virt_tx_config=net_virt_tx.data network_virt_tx.elf
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_bench.data benchmark.elf
	$(OBJCOPY) --update-section .benchmark_config=benchmark_config.data benchmark.elf
	$(OBJCOPY) --update-section .benchmark_config=benchmark_idle_config.data idle.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_ip_collector.data ip_collector.elf
	$(OBJCOPY) --update-section .ip_collector_config=ip_collector_config.data ip_collector.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_ip_collector.data ip_collector.elf


${IMAGE_FILE} $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE) $(ECHO_IMAGES) $(NET_COPY_IMAGES)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)


include ${SDDF}/util/util.mk
include ${SDDF}/network/components/network_components.mk
include ${SDDF}/network/lib_sddf_lwip/lib_sddf_lwip.mk
include ${ETHERNET_DRIVER}/eth_driver.mk
include ${BENCHMARK}/benchmark.mk
include ${TIMER_DRIVER}/timer_driver.mk
include ${SERIAL_DRIVER}/serial_driver.mk
include ${SERIAL_COMPONENTS}/serial_components.mk

qemu: $(IMAGE_FILE)
	$(QEMU) -machine virt,virtualization=on \
			-cpu cortex-a53 \
			-serial mon:stdio \
			-device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
			-m size=2G \
			-nographic \
			-device virtio-net-device,netdev=netdev0 \
			-netdev user,id=netdev0,hostfwd=tcp::1236-:1236,hostfwd=tcp::1237-:1237,hostfwd=udp::1235-:1235 \
			-global virtio-mmio.force-legacy=false \
			-d guest_errors

clean::
	${RM} -f *.elf .depend* $
	find . -name \*.[do] |xargs --no-run-if-empty rm

clobber:: clean
	rm -f *.a
	rm -f ${IMAGE_FILE} ${REPORT_FILE}

-include $(DEPS)
