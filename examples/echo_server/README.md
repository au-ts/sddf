<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Network echo server

This example shows off the networking sub-system by having a
[lwIP](https://savannah.nongnu.org/projects/lwip/) based client talking to an ethernet device.

The client simply accepts RX traffic and sends it back out (hence the name 'echo server').

## Dependencies

Due to the echo server relying on libc functionality, it currently only works with GCC
instead of LLVM like all the other examples. As we use this example to perform benchmarking,
it is important that the functions that lwIP uses from the standard library are optimised
rather than simple implementations.

For now, we rely on the libc packaged with the embedded C toolchains.

### ARM

When targeting ARM boards, the specific toolchain we use for testing and benchmarking the echo
server is the `aarch64-none-elf` GCC toolchain distributed by ARM. You can download it from
[here](https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads).

### RISC-V

When targeting RISC-V boards, we use the embedded GCC toolchain which is `riscv64-none-elf`
or `riscv64-unknown-elf` depending on your environment. This toolchain is not distributed
centrally so below are OS specific instructions:

#### Linux (with apt)

On a Debian-like system, you can do:
```sh
sudo apt install gcc-riscv64-unknown-elf picolibc-riscv64-unknown-elf
```

#### macOS

With Homebrew:
```sh
brew tap riscv-software-src/riscv
brew install riscv-tools
```

## Building

The following platforms are supported:
* imx8mm_evk
* imx8mp_evk
* imx8mq_evk
* maaxboard
* odroidc4
* odroidc2
* qemu_virt_aarch64
* qemu_virt_riscv64
* star64

```sh
make MICROKIT_BOARD=<board> MICROKIT_SDK=<path/to/sdk> MICROKIT_CONFIG=(benchmark/release/debug)
```

## Benchmarking

In order to run the benchmarks, set `MICROKIT_CONFIG=benchmark`. The system has
been designed to interact with [ipbench](https://sourceforge.net/projects/ipbench/)
to take measurements.

> [!NOTE]
> Benchmarking is only supported for AArch64 boards, RISC-V benchmarking is not supported yet,
> see https://github.com/au-ts/sddf/issues/421 for details.

Checks to make before benchmarking:
* Turn off all debug prints.
* Run with LWIP asserts turned off as well (`LWIP_NOASSERT`).
* Make sure compiler optimisations are enabled.
