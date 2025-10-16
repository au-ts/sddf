#
# Copyright 2022, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile is copied into the build directory
# and operated on from there.
#

ifeq ($(strip $(MICROKIT_SDK)),)
$(error MICROKIT_SDK must be specified)
endif

ifeq ($(strip $(SDDF)),)
$(error SDDF must be specified)
endif

BUILD_DIR ?= build
MICROKIT_CONFIG ?= debug
IMAGE_FILE = loader.img
REPORT_FILE = report.txt

ifneq ($(strip $(SMP_CONFIG)),)
	ifneq ($(filter $(strip $(MICROKIT_BOARD)),imx8mp_evk imx8mq_evk odroidc2 qemu_virt_aarch64),)
$(error MICROKIT_BOARD does not support SMP)
	endif
	ifeq ($(wildcard $(SMP_CONFIG)),)
$(error Must specify a valid core configuration file)
	endif
	export MICROKIT_BOARD_SMP := $(addsuffix _multikernel,$(strip $(MICROKIT_BOARD)))
	export SMP_ARG := --smp $(abspath $(SMP_CONFIG))
else
	export MICROKIT_BOARD_SMP := $(strip $(MICROKIT_BOARD))
endif

BOARD_DIR := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD_SMP)/$(MICROKIT_CONFIG)
ARCH := ${shell grep 'CONFIG_SEL4_ARCH  ' $(BOARD_DIR)/include/kernel/gen_config.h | cut -d' ' -f4}
# Toolchain triples have inconsistent naming, below tries to automatically resolve that
ifeq ($(strip $(TOOLCHAIN)),)
	# Get whether the common toolchain triples exist
	TOOLCHAIN_ARCH_NONE_ELF := $(shell command -v $(ARCH)-none-elf-gcc 2> /dev/null)
	TOOLCHAIN_ARCH_UNKNOWN_ELF := $(shell command -v $(ARCH)-unknown-elf-gcc 2> /dev/null)
	# Then check if they are defined and select the appropriate one
	ifdef TOOLCHAIN_ARCH_NONE_ELF
		TOOLCHAIN := $(ARCH)-none-elf
	else ifdef TOOLCHAIN_ARCH_UNKNOWN_ELF
		TOOLCHAIN := $(ARCH)-unknown-elf
	else
$(error "Could not find a $(ARCH) cross-compiler")
	endif
endif
TOOLCHAIN := $(TOOLCHAIN)

CC := $(TOOLCHAIN)-gcc
# Usually, we use the linker directly. Since we're linking against the libc
# for the echo server, we want to use the compiler driver so it can add its
# knowledge of where the libc is located.
LD := $(CC)
AS := $(TOOLCHAIN)-as
AR := $(TOOLCHAIN)-ar
RANLIB := $(TOOLCHAIN)-ranlib
OBJCOPY := $(TOOLCHAIN)-objcopy
DTC := dtc
PYTHON ?= python3

MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

ifeq ($(strip $(MICROKIT_BOARD)), odroidc4)
	export DRIV_DIR := meson
	export SERIAL_DRIV_DIR := meson
	export TIMER_DRV_DIR := meson
	export CPU := cortex-a55
else ifeq ($(strip $(MICROKIT_BOARD)), odroidc2)
	export DRIV_DIR := meson
	export SERIAL_DRIV_DIR := meson
	export TIMER_DRV_DIR := meson
	export CPU := cortex-a53
else ifneq ($(filter $(strip $(MICROKIT_BOARD)),imx8mm_evk imx8mp_evk imx8mq_evk maaxboard),)
	export DRIV_DIR := imx
	export SERIAL_DRIV_DIR := imx
	export TIMER_DRV_DIR := imx
	export CPU := cortex-a53
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_virt_aarch64)
	export DRIV_DIR := virtio
	export SERIAL_DRIV_DIR := arm
	export TIMER_DRV_DIR := arm
	export CPU := cortex-a53
	export QEMU := qemu-system-aarch64
	export QEMU_ARCH_ARGS := -machine virt,virtualization=on -cpu cortex-a53 \
						-device loader,file=$(IMAGE_FILE),addr=0x70000000,cpu-num=0 \
						-serial mon:stdio
else ifeq ($(strip $(MICROKIT_BOARD)), qemu_virt_riscv64)
	export DRIV_DIR := virtio
	export SERIAL_DRIV_DIR := ns16550a
	export TIMER_DRV_DIR := goldfish
	export QEMU := qemu-system-riscv64
	export QEMU_ARCH_ARGS := -machine virt -kernel $(IMAGE_FILE) -serial mon:stdio
else
$(error Unsupported MICROKIT_BOARD given)
endif


TOP := ${SDDF}/examples/echo_server
METAPROGRAM := $(TOP)/meta.py

ECHO_SERVER:=${SDDF}/examples/echo_server
LWIPDIR:=network/ipstacks/lwip/src
BENCHMARK:=$(SDDF)/benchmark
UTIL:=$(SDDF)/util
ETHERNET_DRIVER:=$(SDDF)/drivers/network/$(DRIV_DIR)
SERIAL_COMPONENTS := $(SDDF)/serial/components
SERIAL_DRIVER := $(SDDF)/drivers/serial/$(SERIAL_DRIV_DIR)
TIMER_DRIVER:=$(SDDF)/drivers/timer/$(TIMER_DRV_DIR)
NETWORK_COMPONENTS:=$(SDDF)/network/components
SYSTEM_FILE := echo_server.system
DTS := $(SDDF)/dts/$(MICROKIT_BOARD).dts
DTB := $(MICROKIT_BOARD).dtb

vpath %.c ${SDDF} ${ECHO_SERVER}

IMAGES := eth_driver.elf echo.elf benchmark.elf idle.elf network_virt_rx.elf\
	  network_virt_tx.elf network_copy.elf timer_driver.elf serial_driver.elf serial_virt_tx.elf

ifeq ($(ARCH),aarch64)
	CFLAGS_ARCH := -mcpu=$(CPU) -mstrict-align
else ifeq ($(ARCH),riscv64)
	CFLAGS_ARCH := -march=rv64imafdc -mabi=lp64d
endif

# Echo server example relies on libc functionality, hence only works with GCC
# instead of LLVM. See README for more details.
# Additionally, on x86_64 debian/ubuntu the gcc-riscv64-unknown-elf package is distributed
# without libc. Checks if `picolibc-riscv64-unknown-elf` is installed in that case, and uses it.
LIBC := $(dir $(realpath $(shell $(CC) --print-file-name libc.a)))
PICOLIBC := $(dir $(realpath $(shell $(CC) --print-file-name picolibc.specs)))
ifneq ($(strip $(LIBC)),)
	LDFLAGS_ARCH += -L$(LIBC)
	LIBS_ARCH += -lc
else ifneq ($(strip $(PICOLIBC)),)
	CFLAGS_ARCH += -specs=picolibc.specs
else
	$(error LIBC not found for the selected toolchain: $(TOOLCHAIN))
endif

# Of note here is that we don't specify -nostdlib, as we want libc.
# But we don't want crt0, so add -nostartfiles
CFLAGS := $(CFLAGS_ARCH) \
	  -nostartfiles \
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

LDFLAGS := $(CFLAGS_ARCH) -nostartfiles -ffreestanding -L$(BOARD_DIR)/lib $(LDFLAGS_ARCH)
LIBS := -Wl,--start-group -lmicrokit -Tmicrokit.ld ${LIBS_ARCH} libsddf_util_debug.a -Wl,--end-group

CHECK_FLAGS_BOARD_MD5 := .board_cflags-$(shell echo -- ${CFLAGS} ${MICROKIT_SDK} ${MICROKIT_BOARD} ${MICROKIT_CONFIG} | shasum | sed 's/ *-//')

${CHECK_FLAGS_BOARD_MD5}:
	-rm -f .board_cflags-*
	touch $@

ECHO_OBJS := echo.o utilization_socket.o \
	     udp_echo_socket.o tcp_echo_socket.o

DEPS := $(ECHO_OBJS:.o=.d)

all: loader.img

echo.elf: $(ECHO_OBJS) libsddf_util.a lib_sddf_lwip_echo.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# Need to build libsddf_util_debug.a because it's included in LIBS
# for the unimplemented libc dependencies
${IMAGES}: libsddf_util_debug.a ${CHECK_FLAGS_BOARD_MD5}

$(DTB): $(DTS)
	dtc -q -I dts -O dtb $(DTS) > $(DTB)

$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	$(PYTHON) $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE) --objcopy $(OBJCOPY) $(SMP_ARG)
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .device_resources=ethernet_driver_device_resources.data eth_driver.elf
	$(OBJCOPY) --update-section .net_driver_config=net_driver.data eth_driver.elf
	$(OBJCOPY) --update-section .net_virt_rx_config=net_virt_rx.data network_virt_rx.elf
	$(OBJCOPY) --update-section .net_virt_tx_config=net_virt_tx.data network_virt_tx.elf
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client0_net_copier.data network_copy.elf network_copy0.elf
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client1_net_copier.data network_copy.elf network_copy1.elf || true
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client0.data echo0.elf
	$(OBJCOPY) --update-section .net_client_config=net_client_client0.data echo0.elf
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client0.data echo0.elf
	$(OBJCOPY) --update-section .timer_client_config=timer_client_client1.data echo1.elf || true
	$(OBJCOPY) --update-section .net_client_config=net_client_client1.data echo1.elf || true
	$(OBJCOPY) --update-section .serial_client_config=serial_client_client1.data echo1.elf || true
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client0.data echo0.elf
	$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client1.data echo1.elf || true

${IMAGE_FILE} $(REPORT_FILE): $(IMAGES) $(SYSTEM_FILE)
	$(MICROKIT_TOOL) $(SYSTEM_FILE) --search-path $(BUILD_DIR) --board $(MICROKIT_BOARD_SMP) --config $(MICROKIT_CONFIG) -o $(IMAGE_FILE) -r $(REPORT_FILE)


include ${SDDF}/util/util.mk
include ${SDDF}/network/components/network_components.mk
include ${SDDF}/network/lib_sddf_lwip/lib_sddf_lwip.mk
include ${ETHERNET_DRIVER}/eth_driver.mk
include ${BENCHMARK}/benchmark.mk
include ${TIMER_DRIVER}/timer_driver.mk
include ${SERIAL_DRIVER}/serial_driver.mk
include ${SERIAL_COMPONENTS}/serial_components.mk

qemu: $(IMAGE_FILE)
	$(QEMU) $(QEMU_ARCH_ARGS) \
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
	rm -f ${IMAGE_FILE} ${REPORT_FILE}

-include $(DEPS)
