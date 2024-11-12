<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# seL4 Device Driver Framework

The seL4 Device Driver Framework (sDDF) aims to provide interfaces and protocols for writing and
porting device drivers to run as seL4 user level programs.

The sDDF is currently under-going active research and development and is largely experimental
software.

We are working on developing the protocols and interfaces for various device classes such as:
* Network
* Block
* Serial
* I<sup>2</sup>C
* Audio

There is a large amount of experimentation on-going for each device class, although the design
for the network device class is mostly mature at this point.

The latest design documentation can be found [here](https://trustworthy.systems/projects/drivers/sddf-design.pdf).

More information about the sDDF project can be found on the Trustworthy Systems website
[here](https://trustworthy.systems/projects/drivers/).

## Dependencies

* Microkit SDK 1.4.1
* GNU Make
* Clang and LLVM bintools

The Microkit SDK can be acquired from [here](https://github.com/seL4/microkit/releases/tag/1.4.1).

sDDF is primarily compiled via Makefiles, but the [Zig](https://ziglang.org) build system is also
available. If you are intending on using Zig instead of Make, please see https://ziglang.org/download/.

See the instructions below for installing the rest of the dependencies based on your
machine:

### apt

On apt based Linux distributions run the following commands:

```sh
sudo apt install make llvm lld
```

### Homebrew

On macOS, you can install the dependencies via Homebrew:
```sh
brew install llvm lld make
```

### Nix

There is a Nix flake available in the repository, so you can get a development shell via:
```sh
nix develop
```

## Examples

You can find examples making use of the sDDF in the `examples/` directory. Each example has its
own README for how to build and run it.

Note that some examples may have dependencies in addition to the ones listed in this README.

## Developing sDDF

### Adding a new driver

At a *minimum*, each new driver should have the following:
* An example system in `examples/` showing off the capabilities of the driver if the
  device class does not have an example already.
* The README in the example system should contain the following:
    * A brief description of what hardware functionality the driver supports
    * What the example does and how to compile and run it
* The driver should state exactly what documents where referenced (and what
  version of the documents) to create the driver. If the driver was taken
  from U-Boot or Linux that should also be mentioned along with how to find
  the driver's source code in U-Boot/Linux.
