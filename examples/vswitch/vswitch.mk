#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile is copied into the build directory
# and operated on from there.
#


MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

SUPPORTED_BOARDS := odroidc4 odroidc2 maaxboard \
				imx8mm_evk qemu_virt_aarch64 \
				imx8mq_evk imx8mp_evk \
				imx8mp_iotgate \
				star64 qemu_virt_riscv64 \
				x86_64_generic
TOOLCHAIN ?= clang
MICROKIT_CONFIG ?= debug
SYSTEM_FILE := vswitch.system
IMAGE_FILE := loader.img
REPORT_FILE := report.txt

include ${SDDF}/tools/make/board/common.mk

VSWITCH:= ${SDDF}/examples/vswitch
METAPROGRAM := $(VSWITCH)/meta.py
LWIPDIR := network/ipstacks/lwip/src
UTIL := $(SDDF)/util
ETHERNET_DRIVER := $(SDDF)/drivers/network/$(NET_DRIV_DIR)
SERIAL_COMPONENTS := $(SDDF)/serial/components
UART_DRIVER := $(SDDF)/drivers/serial/$(UART_DRIV_DIR)
TIMER_DRIVER := $(SDDF)/drivers/timer/$(TIMER_DRIV_DIR)
NETWORK_COMPONENTS := $(SDDF)/network/components

SDDF_CUSTOM_LIBC := 1

vpath %.c ${SDDF} ${VSWITCH}

IMAGES := eth_driver.elf client.elf network_virt_rx.elf \
	  network_virt_tx.elf network_copy.elf timer_driver.elf \
	  serial_driver.elf serial_virt_tx.elf network_vswitch.elf


CFLAGS += \
	  -Wno-unused-function \
	  -I$(BOARD_DIR)/include \
	  -I$(SDDF)/include/microkit \
	  -I$(SDDF)/include \
	  -I$(VSWITCH_INCLUDE)/lwip \
	  -I$(LWIPDIR)/include \
	  -I$(LWIPDIR)/include/ipv4 \
	  -I $(VSWITCH)/include \
	  -MP


# Suppress warning from lwIP
CFLAGS += -Wno-tautological-constant-out-of-range-compare

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a \
	--end-group

VSWITCH_OBJS := client.o icmp.o

DEPS := $(VSWITCH_OBJS:.o=.d)

all: loader.img

client.elf: $(VSWITCH_OBJS) libsddf_util.a lib_sddf_lwip_client.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# Need to build libsddf_util_debug.a because it's included in LIBS
# for the unimplemented libc dependencies
${IMAGES}: libsddf_util_debug.a

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	cp network_copy.elf network_copy0.elf
	cp network_copy.elf network_copy1.elf
	cp network_copy.elf network_copy2.elf
	cp network_copy.elf network_copy3.elf
ifneq ($(strip $(DTS)),)
	$(PYTHON)\
	    $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) \
	    --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
else
	$(PYTHON)\
	    $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) \
	    --output . --sdf $(SYSTEM_FILE)
endif
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .device_resources=ethernet_driver_device_resources.data eth_driver.elf
	$(OBJCOPY) --update-section .net_driver_config=net_driver.data eth_driver.elf
	$(OBJCOPY) --update-section .net_virt_rx_config=net_virt_rx.data network_virt_rx.elf
	$(OBJCOPY) --update-section .net_virt_tx_config=net_virt_tx.data network_virt_tx.elf
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client0_net_copier.data network_copy0.elf
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client1_net_copier.data network_copy1.elf
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client2_net_copier.data network_copy2.elf
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client3_net_copier.data network_copy3.elf
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client0.data client0.elf
	$(OBJCOPY) --update-section .net_client_config=net_client_client0.data client0.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client0.data client0.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client1.data client1.elf
	$(OBJCOPY) --update-section .net_client_config=net_client_client1.data client1.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client1.data client1.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client2.data client2.elf
	$(OBJCOPY) --update-section .net_client_config=net_client_client2.data client2.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client2.data client2.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client3.data client3.elf
	$(OBJCOPY) --update-section .net_client_config=net_client_client3.data client3.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client3.data client3.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client0.data client0.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client1.data client1.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client2.data client2.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client3.data client3.elf
	$(OBJCOPY) --update-section .net_vswitch_config=net_vswitch.data network_vswitch.elf
	touch $@

${IMAGE_FILE} $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) \
	--board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) \
	-o $(IMAGE_FILE) -r $(REPORT_FILE)


include ${SDDF}/util/util.mk
include ${SDDF}/network/components/network_components.mk
include ${SDDF}/network/lib_sddf_lwip/lib_sddf_lwip.mk
include ${ETHERNET_DRIVER}/eth_driver.mk
include ${TIMER_DRIVER}/timer_driver.mk
include ${UART_DRIVER}/serial_driver.mk
include ${SERIAL_COMPONENTS}/serial_components.mk

qemu: $(IMAGE_FILE)
	$(QEMU) $(QEMU_ARCH_ARGS) $(QEMU_NET_ARGS) \
		-nographic \
		-netdev user,id=netdev0,\
		-global virtio-mmio.force-legacy=false \
		-d guest_errors -smp 4

clean::
	${RM} -f *.elf .depend* $
	find . -name \*.[do] |xargs --no-run-if-empty rm

clobber:: clean
	rm -f ${IMAGE_FILE} ${REPORT_FILE}

-include $(DEPS)
