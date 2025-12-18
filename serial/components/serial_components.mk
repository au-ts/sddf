#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile snippet builds the serial RX and TX virtualisers
# it should be included into your project Makefile
#
# NOTES:
# Generates serial_virt_rx.elf serial_virt_tx.elf
#

SERIAL_IMAGES:= serial_virt_rx.elf serial_virt_tx.elf
SERIAL_COMPONENT_OBJ := $(addprefix serial/components/, serial_virt_tx.o serial_virt_rx.o)

CFLAGS_serial := -I ${SDDF}/include

CHECK_SERIAL_FLAGS_MD5:=.serial_cflags-$(shell echo -- ${CFLAGS} ${CFLAGS_serial} | shasum | sed 's/ *-//')

# Detect compiler type for consistent flag usage
CC_IS_CLANG := $(shell $(CC) --version 2>/dev/null | grep -q clang && echo 1 || echo 0)

ARCH := ${shell grep 'CONFIG_SEL4_ARCH  ' $(BOARD_DIR)/include/kernel/gen_config.h | cut -d' ' -f4}
$(info [serial_components] Detected ARCH: $(ARCH) from $(BOARD_DIR))

ifeq ($(ARCH),aarch64)
    PANCAKE_TARGET := arm8
    ifeq ($(CC_IS_CLANG),1)
        ASM_FLAGS := -target aarch64-none-elf $(if $(CPU),-mcpu=$(CPU))
    else
        ASM_FLAGS := $(if $(CPU),-mcpu=$(CPU))
    endif
else ifeq ($(ARCH),riscv64)
    PANCAKE_TARGET := riscv
    ifeq ($(CC_IS_CLANG),1)
        ASM_FLAGS := -target riscv64-none-elf -march=rv64imafdc
    else
        ASM_FLAGS := -march=rv64imafdc -mabi=lp64d
    endif
else
    $(warning [serial_components] Unknown ARCH '$(ARCH)', defaulting to arm8)
    PANCAKE_TARGET := arm8
endif

$(info [serial_components] Using PANCAKE_TARGET: $(PANCAKE_TARGET))

${CHECK_SERIAL_FLAGS_MD5}:
	-rm -f .serial_cflags-*
	touch $@

${SERIAL_COMPONENT_OBJ}: |serial/components
${SERIAL_COMPONENT_OBJ}: ${CHECK_SERIAL_FLAGS_MD5}

SERIAL_QUEUE_INCLUDE := ${SDDF}/include/sddf/serial

ifeq ($(PANCAKE_SERIAL_VIRT_RX),1)
SERIAL_VIRT_RX_PNK = ${UTIL}/util.pnk \
	${SERIAL_QUEUE_INCLUDE}/queue.pnk \
	${SDDF}/serial/components/virt_rx.pnk

serial_virt_rx.elf: serial/components/virt_rx_pnk.o serial/components/serial_virt_rx.o pancake_ffi.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/components/virt_rx_pnk.o: serial/components/virt_rx_pnk.S
	$(CC) $(ASM_FLAGS) -c $< -o $@

serial/components/virt_rx_pnk.S: $(SERIAL_VIRT_RX_PNK) | serial/components
	cat $(SERIAL_VIRT_RX_PNK) | cpp -P | $(CAKE_COMPILER) --target=$(PANCAKE_TARGET) --pancake --main_return=true > $@

serial/components/serial_virt_rx.o: ${SDDF}/serial/components/virt_rx.c
	${CC} ${CFLAGS} ${CFLAGS_serial} -DPANCAKE_SERIAL -o $@ -c $<
else
serial_virt_rx.elf: serial/components/serial_virt_rx.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/components/serial_virt_rx.o: ${SDDF}/serial/components/virt_rx.c
	${CC} ${CFLAGS} ${CFLAGS_serial} -o $@ -c $<
endif

ifeq ($(PANCAKE_SERIAL_VIRT_TX),1)
SERIAL_VIRT_TX_PNK = ${UTIL}/util.pnk \
	${SERIAL_QUEUE_INCLUDE}/queue.pnk \
	${SDDF}/serial/components/virt_tx.pnk

serial_virt_tx.elf: serial/components/virt_tx_pnk.o serial/components/serial_virt_tx.o pancake_ffi.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/components/virt_tx_pnk.o: serial/components/virt_tx_pnk.S
	$(CC) $(ASM_FLAGS) -c $< -o $@

serial/components/virt_tx_pnk.S: $(SERIAL_VIRT_TX_PNK) | serial/components
	cat $(SERIAL_VIRT_TX_PNK) | cpp -P | $(CAKE_COMPILER) --target=$(PANCAKE_TARGET) --pancake --main_return=true > $@

serial/components/serial_virt_tx.o: ${SDDF}/serial/components/virt_tx.c
	${CC} ${CFLAGS} ${CFLAGS_serial} -DPANCAKE_SERIAL -o $@ -c $<
else
serial_virt_tx.elf: serial/components/serial_virt_tx.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/components/serial_virt_tx.o: ${SDDF}/serial/components/virt_tx.c
	${CC} ${CFLAGS} ${CFLAGS_serial} -o $@ -c $<
endif

serial/components:
	mkdir -p $@

clean::
	rm -f serial_virt_[rt]x.[od] .serial_cflags-*
	rm -f serial/components/virt_[rt]x_pnk.[So]

clobber::
	rm -f ${SERIAL_IMAGES}

-include serial/components/serial_virt_rx.d
-include serial/components/serial_virt_tx.d
-include serial/components/virt_rx.d
-include serial/components/virt_tx.d
