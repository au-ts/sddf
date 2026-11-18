#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#

ifeq ($(strip ${FB_IMG}),)
$(error FB_IMG must be specified)
endif

ifeq ($(strip ${BLOB}),)
$(error BLOB must be specified)
endif

ifeq (, $(shell which convert))
$(error "convert is not available. Please install imagemagick")
endif

SUPPORTED_BOARDS := qemu_virt_aarch64
ifeq ($(strip ${TOOLCHAIN}),)
	TOOLCHAIN := clang
endif
SDDF_CUSTOM_LIBC := 1
ifneq ($(strip ${BLOB}), 0)
CFLAGS_gpu := -DGPU_BLOB_SUPPORT
else
CFLAGS_gpu :=
endif

include ${SDDF}/tools/make/sddf.mk

TOP := ${SDDF}/examples/gpu
METAPROGRAM := ${TOP}/meta.py

IMAGES := gpu_driver.elf client.elf gpu_virt.elf timer_driver.elf
CFLAGS += -Wno-unused-function -Werror -Wno-unused-command-line-argument \
	  -I${SDDF}/include \
	  -I${SDDF}/include/microkit
LDFLAGS := -L${BOARD_DIR}/lib
LIBS := --start-group -lmicrokit -Tmicrokit.ld libsddf_util_debug.a --end-group

IMAGE_FILE := loader.img
REPORT_FILE := report.txt
SYSTEM_FILE := gpu.system

# Blob resources need guest RAM backed by memfd so QEMU can create udmabufs
# (Linux only). Without blob, plain RAM works on any host, including macOS.
ifneq ($(strip ${BLOB}), 0)
	QEMU_OPTIONS := -device virtio-gpu-device,edid=off,blob=on,max_outputs=1,indirect_desc=off,event_idx=off
	QEMU_MEM_OPTIONS := -machine memory-backend=main-mem -object memory-backend-memfd,id=main-mem,size=2G
else
	QEMU_OPTIONS := -device virtio-gpu-device,edid=off,blob=off,max_outputs=1,indirect_desc=off,event_idx=off
	QEMU_MEM_OPTIONS :=
endif

QEMU_CMD := ${QEMU} -machine virt,virtualization=on \
			-device loader,file=${IMAGE_FILE},addr=0x70000000,cpu-num=0 \
			-m size=2G \
			${QEMU_MEM_OPTIONS} \
			${QEMU_OPTIONS} \
			-serial mon:stdio \
			-global virtio-mmio.force-legacy=false \
			-d guest_errors
			# -trace enable=virtio*

all: ${IMAGE_FILE}

${IMAGES}: libsddf_util_debug.a

CHECK_GPU_CLI_FLAGS_MD5 := .gpu_cli_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_gpu} | shasum | sed 's/ *-//')

${CHECK_GPU_CLI_FLAGS_MD5}:
	-rm -f .gpu_cli_cflags-*
	touch $@

fb_img.bgra: ${FB_IMG}
	convert -auto-orient -depth 8 -size $(shell convert $< -print "%wx%h" /dev/null) $< bgra:$@

client.o: ${TOP}/client.c ${FB_IMG} ${CHECK_GPU_CLI_FLAGS_MD5}
	${CC} -c ${CFLAGS} ${CFLAGS_gpu} \
		-DFB_IMG_WIDTH=$(shell convert ${FB_IMG} -auto-orient -print "%w" /dev/null) \
		-DFB_IMG_HEIGHT=$(shell convert ${FB_IMG} -auto-orient -print "%h" /dev/null) \
		$< -o $@

fb_img.o: ${TOP}/fb_img.S fb_img.bgra
	${CC} ${CFLAGS} -c -DFB_IMG_PATH=\"fb_img.bgra\" $< -o $@

client.elf: client.o fb_img.o
	${LD} ${LDFLAGS} $^ ${LIBS} -o $@

${SYSTEM_FILE}: ${METAPROGRAM} ${IMAGES} ${DTB}
	$(PYTHON) $(METAPROGRAM) --board $(MICROKIT_BOARD) --dtb $(DTB) --output . --sdf $(SYSTEM_FILE)
	$(OBJCOPY) --update-section .device_resources=gpu_driver_device_resources.data gpu_driver.elf
	$(OBJCOPY) --update-section .gpu_driver_config=gpu_driver_gpu_driver_config.data gpu_driver.elf
	$(OBJCOPY) --update-section .gpu_virt_config=gpu_virt_gpu_virt_config.data gpu_virt.elf
	$(OBJCOPY) --update-section .gpu_client_config=client_gpu_client_config.data client.elf
	$(OBJCOPY) --update-section .device_resources=timer_driver_device_resources.data timer_driver.elf
	$(OBJCOPY) --update-section .timer_client_config=client_timer_client_config.data client.elf
	touch $@

${IMAGE_FILE} ${REPORT_FILE}: ${IMAGES} ${SYSTEM_FILE}
	${MICROKIT_TOOL} ${SYSTEM_FILE} --search-path ${BUILD_DIR} --board ${MICROKIT_BOARD} --config ${MICROKIT_CONFIG} -o ${IMAGE_FILE} -r ${REPORT_FILE}

qemu: ${IMAGE_FILE}
	${QEMU_CMD}

clean::
	rm -f client.o fb_img.o fb_img.bgra
clobber:: clean
	rm -f client.elf ${IMAGE_FILE} ${REPORT_FILE} ${SYSTEM_FILE} *.data
