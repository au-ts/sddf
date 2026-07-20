#!/usr/bin/env sh

# cd /Users/terrybai/ts/sddf/examples/echo_server && \
# rm -rf build && \
# make -j$(nproc) BUILD_DIR=build MICROKIT_BOARD=x86_64_generic X86_BOARD=qemu_virt_x86 MICROKIT_CONFIG=debug MICROKIT_SDK=/Users/terrybai/ts/microkit/release/microkit-sdk-2.2.0-dev qemu

cd /Users/terrybai/ts/sddf/examples/echo_server && \
rm -rf build && \
# make -j$(nproc) BUILD_DIR=build MICROKIT_BOARD=x86_64_generic X86_BOARD=qemu_virt_x86 MICROKIT_CONFIG=debug MICROKIT_SDK=/Users/terrybai/ts/microkit/release/microkit-sdk-2.2.0-dev qemu
make -j$(nproc) BUILD_DIR=build MICROKIT_BOARD=x86_64_generic X86_BOARD=vb_105 MICROKIT_CONFIG=debug MICROKIT_SDK=/Users/terrybai/ts/microkit/release/microkit-sdk-2.2.0-dev && \
mq.sh run -s vb_105 -f ./build/sel4.elf -f ./build/loader.img -c "fnjkeqhtreqfgkjadfg"
# /Users/terrybai/tmp/machine_queue/mq.sh run -s viscous -f ./build/sel4.elf -f ./build/loader.img -c "fnjkeqhtreqfgkjadfg"
