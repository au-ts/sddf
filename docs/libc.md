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
high-performance use-cases such as networking we need optimised implementations
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

If you with to use the vendored libc in your sDDF system, the build system can
add the provided libc functions to the sDDF [utility](/util/util.mk) library.
All the existing sDDF example systems already utilise this library for
functionalities like
[printing](/docs/serial/serial.md#building-components-and-libraries) in either
its serial (`libsddf_util.a`) or debug (`libsddf_util_debug.a`) form.

To simplify this we have created the `SDDF_CUSTOM_LIBC` configuration variable.

#### Makefile

First, you must set the custom libc configuration variable to 1 in your system's
makefile:

```sh
SDDF_CUSTOM_LIBC := 1
```

You also must ensure the sDDF utility library make snippet is included, and that
one or more utility libraries are a target of your makefile. You will also need
to ensure that any components depending on the library are tracked:

```sh
include ${SDDF}/util/util.mk

${IMAGES}: libsddf_util_debug.a
```

The utility library make snippet will then build and archive the libc functions,
and add the required include path to your system's `CFLAGS`. 

Finally, you will need to ensure that all components requiring the libc
functions are linked with the desired utility library (this is typically done by
adding `libsddf_util_debug` to your linker `LIBS`).

Note that compiler builtins are preferred when available; headers map standard
functions to `__builtin_*` equivalents using feature detection.

## External libc (OS-Provided)

When building sDDF components as part of an operating system that provides its
own libc (e.g. musl), the vendored implementations should be disabled. This is
done by default when `SDDF_CUSTOM_LIBC` is not defined.

To allow libc dependencies to still be tracked when an external libc is to be
used, we have created a distinct `SDDF_LIBC_INCLUDE` path/configuration variable
that typically contains the path of the external libc headers. This works best
when this path is a makefile target in your external system's makefile. You can
read more about how this is used in LionsOS
[here](https://lionsos.org/docs/use/language_support/libc/).

### Usage

To use an external libc:

#### Makefile

Ensure that `SDDF_CUSTOM_LIBC` **is not set**.

Set `SDDF_LIBC_INCLUDE` to the external libc header path, and ensure this
definition is visible to all sDDF component makefiles. If you are building this
path and headers, ensure there is a matching target in your makefile. sDDF
components treat this as an order-only prerequisite to ensure headers are
available before compilation (avoiding unnecessary rebuilds). 

Add the external libc header path (typically `SDDF_LIBC_INCLUDE`) to the
`CFLAGS` of the sDDF components. Also ensure that sDDF components are linked
with the external libc when required.

### Developing

Typically while developing an sDDF example system or component, the vendored
libc included in the utility library will be used. Since components typically
depend on this library for functionality outside of just libc, most example
systems list the utility library as a dependency for all components, thus
per-component libc dependency can easily be ignored.

However, when an external libc is used, it is important to keep track of
per-component libc dependency to avoid future build dependency issues. When
creating a new make snippet for a component or system, you must ensure that any
components requiring libc functionalities are marked as having this
pre-requisite using `SDDF_LIBC_INCLUDE`:

```sh
network/imx/ethernet.o: ... | $(SDDF_LIBC_INCLUDE)
    ...
```
