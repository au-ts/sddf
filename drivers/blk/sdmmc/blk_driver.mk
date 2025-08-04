#
# Copyright 2023, Colias Group, LLC
#
# SPDX-License-Identifier: BSD-2-Clause
#


# Get current dir
SDMMC_DRIVER_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

# Allow for different build configurations (default is debug)
microkit_sdk_config_dir := $(MICROKIT_SDK)/board/$(MICROKIT_BOARD)/$(MICROKIT_CONFIG)
sel4_include_dirs := $(microkit_sdk_config_dir)/include

# Ensure build directory exists
$(BUILD_DIR):
	@echo "Creating build directory $(BUILD_DIR)..."
	mkdir -p $@

blk/sdmmc/meson/sddf_helper.o: $(SDMMC_DRIVER_DIR)/src/sddf_helper.c |blk/sdmmc/meson
	$(CC) -c $(CFLAGS) $< -o $@

blk/sdmmc/meson/libsddfblk.a: blk/sdmmc/meson/sddf_helper.o |blk/sdmmc/meson
	${AR} rcs $@ $<

blk/sdmmc/meson:
	mkdir -p $@

# Main build target
blk_driver.elf: $(BUILD_DIR) blk/sdmmc/meson/libsddfblk.a
	cp blk/sdmmc/meson/libsddfblk.a $(abspath ${SDMMC_DRIVER_DIR})
	@cd $(abspath ${SDMMC_DRIVER_DIR}) && \
	echo "Building blk_driver.elf for board $(MICROKIT_BOARD)..." && \
	echo "MICROKIT SDK config directory: $(microkit_sdk_config_dir)" && \
	echo "SEl4 include directories: $(sel4_include_dirs)" && \
	SEL4_INCLUDE_DIRS=$(abspath $(sel4_include_dirs)) \
	cargo build \
		-Z build-std=core,alloc,compiler_builtins \
		-Z build-std-features=compiler-builtins-mem \
		--target-dir $(BUILD_DIR)/blk/sdmmc/meson/ \
		--target support/targets/aarch64-sel4-microkit-minimal.json \
		--features "meson"
	cp $(BUILD_DIR)/blk/sdmmc/meson/aarch64-sel4-microkit-minimal/debug/blk_driver.elf $(BUILD_DIR)
	echo "Build complete: $(TARGET_ELF)"