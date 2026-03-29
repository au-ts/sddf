#!/usr/bin/env sh

cd /Users/terrybai/ts/sddf/examples/pci && \
rm -rf build && \
make BUILD_DIR=build MICROKIT_BOARD=x86_64_generic X86_BOARD=qemu_virt_x86 MICROKIT_CONFIG=debug MICROKIT_SDK=/Users/terrybai/ts/microkit/release/microkit-sdk-2.1.0-dev qemu
