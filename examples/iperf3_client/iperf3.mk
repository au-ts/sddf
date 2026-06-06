MICROKIT_TOOL ?= $(MICROKIT_SDK)/bin/microkit

IPERF3_CLIENT := ${SDDF}/examples/iperf3_client

SUPPORTED_BOARDS := odroidc4 odroidc2 maaxboard \
		    imx8mm_evk qemu_virt_aarch64 \
		    imx8mq_evk imx8mp_evk \
		    imx8mp_iotgate \
		    star64 qemu_virt_riscv64
TOOLCHAIN ?= clang
MICROKIT_CONFIG ?= debug
SYSTEM_FILE := iperf3.system
IMAGE_FILE := loader.img
REPORT_FILE := report.txt

include ${SDDF}/tools/make/board/common.mk

METAPROGRAM := $(IPERF3_CLIENT)/meta.py
LWIPDIR := network/ipstacks/lwip/src
BENCHMARK := $(SDDF)/benchmark
UTIL := $(SDDF)/util
ETHERNET_DRIVER := $(SDDF)/drivers/network/$(NET_DRIV_DIR)
ETHERNET_CONFIG_INCLUDE := ${IPERF3_CLIENT}/include/ethernet_config
SERIAL_COMPONENTS := $(SDDF)/serial/components
UART_DRIVER := $(SDDF)/drivers/serial/$(UART_DRIV_DIR)
TIMER_DRIVER := $(SDDF)/drivers/timer/$(TIMER_DRIV_DIR)
NETWORK_COMPONENTS := $(SDDF)/network/components

SDDF_CUSTOM_LIBC := 1

vpath %.c ${SDDF} ${IPERF3_CLIENT}

IMAGES := eth_driver.elf iperf3_client.elf benchmark.elf idle.elf \
	  network_virt_rx.elf network_virt_tx.elf network_copy.elf \
	  timer_driver.elf serial_driver.elf serial_virt_tx.elf serial_virt_rx.elf

CFLAGS += \
	  -Wno-unused-function \
	  -I$(BOARD_DIR)/include \
	  -I$(SDDF)/include/microkit \
	  -I$(SDDF)/include \
	  -I${IPERF_INCLUDE}/lwip \
	  -I${ETHERNET_CONFIG_INCLUDE} \
	  -I$(LWIPDIR)/include \
	  -I$(LWIPDIR)/include/ipv4 \
	  -I $(IPERF3_CLIENT)/include \
	  -MP

CFLAGS += -Wno-tautological-constant-out-of-range-compare

# NUM_STREAMS / TARGET_BW_MBPS used to be compile-time; they are now runtime
# arguments to the serial `start` command (ctrl.num_streams / ctrl.target_bw_mbps),
# so no -D flags are needed for them anymore.

# Both protocols are compiled into every image; the protocol is chosen at runtime
# by the serial `start [tcp|udp] ...` command. PROTOCOL= only sets the default
# used when the token is omitted (udp => -DIPERF3_DEFAULT_UDP).
PROTOCOL ?= udp
ifeq ($(PROTOCOL),udp)
CFLAGS += -DIPERF3_DEFAULT_UDP
endif

# Note: SERVER_IP is still forwarded to meta.py (it injects per-client
# app_config.server_ip/server_port). The old -DSERVER_IP_A..D compile-time
# fallback was removed — the server address is now a runtime `start` argument.

LDFLAGS := -L$(BOARD_DIR)/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a \
	--end-group

IPERF_OBJS := iperf3_client.o iperf3_ctrl.o iperf3_stream_tcp.o iperf3_stream_udp.o utilization_socket.o

DEPS := $(IPERF_OBJS:.o=.d)

all: loader.img

iperf3_client.elf: $(IPERF_OBJS) libsddf_util.a lib_sddf_lwip_iperf_client.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

${IMAGES}: libsddf_util_debug.a

# meta.py performs all per-client and per-core benchmark objcopy (the number of
# client/benchmark/idle ELFs varies with the core-allocation file). Only the
# single-instance driver/virtualiser sections are patched here.
$(SYSTEM_FILE): $(METAPROGRAM) $(IMAGES) $(DTB)
	SERVER_IP=$(SERVER_IP) $(PYTHON)\
	    $(METAPROGRAM) --sddf $(SDDF) --board $(MICROKIT_BOARD) \
	    --dtb $(DTB) --output . --sdf $(SYSTEM_FILE) --objcopy $(OBJCOPY) --smp $(SMP_CONFIG)
	$(OBJCOPY) --update-section .device_resources=serial_driver_device_resources.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_driver_config=serial_driver_config.data serial_driver.elf
	$(OBJCOPY) --update-section .serial_virt_tx_config=serial_virt_tx.data serial_virt_tx.elf
	$(OBJCOPY) --update-section .serial_virt_rx_config=serial_virt_rx.data serial_virt_rx.elf
	$(OBJCOPY) --update-section .device_resources=ethernet_driver_device_resources.data eth_driver.elf
	$(OBJCOPY) --update-section .net_driver_config=net_driver.data eth_driver.elf
	$(OBJCOPY) --update-section .net_virt_rx_config=net_virt_rx.data network_virt_rx.elf
	$(OBJCOPY) --update-section .net_virt_tx_config=net_virt_tx.data network_virt_tx.elf
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
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
		-netdev user,id=netdev0 \
		-global virtio-mmio.force-legacy=false \
		-d guest_errors -smp 4

clean::
	${RM} -f *.elf .depend* $
	find . -name \*.[do] |xargs --no-run-if-empty rm
	# lib_sddf_lwip.mk's clean only wipes the suffix-less lib_sddf_lwip_out/.
	# We link the suffixed variant lib_sddf_lwip_iperf_client.a, whose objects
	# live in lib_sddf_lwip_out_iperf_client/ and whose .a is only removed by
	# clobber. Remove both here so lwipopts.h edits always take effect on rebuild.
	${RM} -rf lib_sddf_lwip_out_iperf_client
	${RM} -f lib_sddf_lwip_iperf_client.a

clobber:: clean
	rm -f ${IMAGE_FILE} ${REPORT_FILE}

-include $(DEPS)