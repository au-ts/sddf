<!--
    Copyright 2026, UNSW
    SPDX-License-Identifier: BSD-2-Clause
-->
# Pancake components in sDDF

[Pancake](https://cakeml.org/pancake) is a systems programming language with a
verified compiler. We are using Pancake to implement verified OS components
that were previously written in C, and by converting annotated Pancake code
into the [Viper](https://viper.ethz.ch/) verification language using a
[transpiler](https://trustworthy.systems/projects/pancake-transpiler/), these
OS components can be verified for functional correctness and more.

To build Pancake components, the Pancake compiler should be available.
Currently, the compiler shares the same binary as the CakeML compiler `cake`
available [here](https://cakeml.org/download). In addition, the C toolchain
should be accessible, because the linker and the preprocessor are still
required to build the full image.

We provide some commonly used definitions for Pancake components:
- [`util/pancake_common.c`](../util/pancake_common.c) provides necessary
  helper functions for Pancake components.
- [`util/pancake_ffi.c`](../util/pancake_ffi.c) allows Pancake code to call
  external sDDF OS functions.

For an example of writing a Pancake component, see the serial driver example
[here](../drivers/serial/arm).

For an introduction to Pancake programming in general, see the document
[here](https://github.com/CakeML/cakeml/blob/pan_howto/pancake/how-to.md).
