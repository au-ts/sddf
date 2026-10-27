#
# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile is copied into the build directory
# and operated on from there.
#


MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

SUPPORTED_BOARDS := \
			imx8mm_evk \
			imx8mp_evk \
			imx8mq_evk \
			imx8mp_iotgate \
			maaxboard \
			odroidc2 \
			odroidc4 \
			qemu_virt_aarch64 \
			qemu_virt_riscv64 \
			rock3b \
			rockpro64 \
			star64 \
			x86_64_generic \
			rpi4b_1gb \
			zcu102
TOOLCHAIN ?= clang
MICROKIT_CONFIG ?= debug
SYSTEM_FILE := vswitch.system
IMAGE_FILE := loader.img
REPORT_FILE := report.txt

SDDF_CUSTOM_LIBC := 1
include ${SDDF}/tools/make/sddf.mk

VSWITCH:= ${SDDF}/examples/vswitch
METAPROGRAM := $(VSWITCH)/meta.py

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
		--dtb $(DTB) --output . --sdf $(SYSTEM_FILE) --objcopy $(OBJCOPY)
else
	$(PYTHON)\
		$(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) \
		--output . --sdf $(SYSTEM_FILE) --objcopy $(OBJCOPY)
endif
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx_serial_virt_tx_config.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .device_resources=eth_driver_device_resources.data eth_driver.elf
	$(OBJCOPY) --update-section .net_driver_config=eth_driver_net_driver_config.data eth_driver.elf
	$(OBJCOPY) --update-section .net_virt_rx_config=network_virt_rx_net_virt_rx_config.data network_virt_rx.elf
	$(OBJCOPY) --update-section .net_virt_tx_config=network_virt_tx_net_virt_tx_config.data network_virt_tx.elf
	$(OBJCOPY) --update-section .net_copy_config=network_copy0_net_copy_config.data network_copy0.elf
	$(OBJCOPY) --update-section .net_copy_config=network_copy1_net_copy_config.data network_copy1.elf
	$(OBJCOPY) --update-section .net_copy_config=network_copy2_net_copy_config.data network_copy2.elf
	$(OBJCOPY) --update-section .net_copy_config=network_copy3_net_copy_config.data network_copy3.elf
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=client0_timer_client_config.data client0.elf
	$(OBJCOPY) --update-section .net_client_config=client0_net_client_config.data client0.elf
	$(OBJCOPY) --update-section .serial_client_config=client0_serial_client_config.data client0.elf
	$(OBJCOPY) --update-section .timer_client_config=client1_timer_client_config.data client1.elf
	$(OBJCOPY) --update-section .net_client_config=client1_net_client_config.data client1.elf
	$(OBJCOPY) --update-section .serial_client_config=client1_serial_client_config.data client1.elf
	$(OBJCOPY) --update-section .timer_client_config=client2_timer_client_config.data client2.elf
	$(OBJCOPY) --update-section .net_client_config=client2_net_client_config.data client2.elf
	$(OBJCOPY) --update-section .serial_client_config=client2_serial_client_config.data client2.elf
	$(OBJCOPY) --update-section .timer_client_config=client3_timer_client_config.data client3.elf
	$(OBJCOPY) --update-section .net_client_config=client3_net_client_config.data client3.elf
	$(OBJCOPY) --update-section .serial_client_config=client3_serial_client_config.data client3.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=client0_lib_sddf_lwip_config.data client0.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=client1_lib_sddf_lwip_config.data client1.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=client2_lib_sddf_lwip_config.data client2.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=client3_lib_sddf_lwip_config.data client3.elf
	$(OBJCOPY) --update-section .net_vswitch_config=network_vswitch_net_vswitch_config.data network_vswitch.elf
	touch $@


${IMAGE_FILE} $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) \
	--board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) \
	-o $(IMAGE_FILE) -r $(REPORT_FILE)

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
