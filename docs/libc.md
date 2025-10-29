<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->
# libc Usage in sDDF Components

sDDF supports two modes for accessing standard C library functionality,
depending on whether an external libc is available in the build environment.

## Vendored libc (Internal sDDF Implementation)

### Motivation

While sDDF components do not need a full libc like you would expect on an OS
like Linux, there are certain basic functions such as `memcpy` or `strlen` that
are expected.

It is trivial to write our own implementations of these functions, however for
high-peformance use-cases such as networking we need optimised implementations
which is why we vendor them.

### Overview

sDDF includes a minimal subset of the C standard library, vendored from
[newlib](https://sourceware.org/git/newlib-cygwin.git) at commit
[4613a9a9799792a53444576de61bd1569f346ffa](https://sourceware.org/git/?p=newlib-cygwin.git;a=commit;h=4613a9a9799792a53444576de61bd1569f346ffa)
for `aarch64` and `riscv64` architectures, suitable for use in environments
without a full libc.

The following functions are provided:

- `memcmp`
- `memcpy`
- `memmove`
- `memset`
- `strcmp`
- `strcpy`
- `strlen`
- `strncmp`

Additionally, internal implementations of `atoi` and `strcat` are available.

### Usage

To use the vendored libc:

- Set `SDDF_CUSTOM_LIBC := 1` in your component's Makefile.
- This enables inclusion of the vendored source files and headers from
`util/custom_libc`.
- The build system will automatically add the necessary object files and include
paths.

Note that compiler builtins are preferred when available; headers map standard
functions to `__builtin_*` equivalents using feature detection.

## External libc (OS-Provided)

When building sDDF components as part of an operating system that provides its
own libc (e.g. musl), the vendored implementations should be disabled.

### Usage

To use an external libc:

- **Do not set** `SDDF_CUSTOM_LIBC`.
- Define `SDDF_LIBC_INCLUDE` to point to the OS libc headers in your component's
Makefile.
- Add this as an include directory to `CFLAGS`.
- The Makefile must provide a target that builds these headers prior to driver
compilation.
- sDDF components treat this as an order-only prerequisite to ensure headers
are available before compilation while avoiding unnecessary rebuilds.
