<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->
# Availability of standard library string and memory functions

The sDDF has vendored a subset of the C standard library from
[newlib](https://sourceware.org/git/newlib-cygwin.git), as of commit
[4613a9a9799792a53444576de61bd1569f346ffa](https://sourceware.org/git/?p=newlib-cygwin.git;a=commit;h=4613a9a9799792a53444576de61bd1569f346ffa).

The following are provided (optimised for the `aarch64`, `x86_64`, `riscv64`
architectures):
- `memcmp`
- `memcpy`
- `memmove`
- `memset`
- `strcmp`
- `strcpy`
- `strlen`
- `strncmp`

Additionally, internal implementations of `atoi` and `strcat` are available.

## Usage

Simply add `SDDF_CUSTOM_LIBC := 1` to your Makefile snippet. Please refer to
the `echo_server` example for one such use case.

## Motivation

While sDDF components do not need a full libc like you would expect on an OS
like Linux, there are certain basic functions such as `memcpy` or `strlen` that
are expected.

It is trivial to write our own implementations of these functions, however for
high-peformance use-cases such as networking we need optimised implementations
which is why we vendor them.
