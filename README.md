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

* [Microkit SDK 2.0.1](https://github.com/seL4/microkit/releases/tag/2.0.1)
* GNU Make
* Clang and LLVM bintools
* Device Tree Compiler
* Python (3.9 or higher)

sDDF is primarily compiled via Makefiles, but the [Zig](https://ziglang.org) build system is also
available. If you are intending on using Zig instead of Make, please see https://ziglang.org/download/.

See the instructions below for installing the rest of the dependencies based on your
machine:

### apt

On apt based Linux distributions run the following commands:

```sh
sudo apt install make llvm lld device-tree-compiler python3 python3-pip
pip3 install sdfgen==0.23.1
```

If you get `error: externally-managed-environment`
when installing via pip, instead run:
```sh
# sdfgen is an isolated package and does not depend on anything
# else so it will not break any system packages.
pip3 install --break-system-packages sdfgen==0.23.1
```

#### Microkit SDK

```sh
wget https://github.com/seL4/microkit/releases/download/2.0.1/microkit-sdk-2.0.1-linux-x86-64.tar.gz
tar xf microkit-sdk-2.0.1-linux-x86-64.tar.gz
```

### Homebrew

On macOS, you can install the dependencies via Homebrew:
```sh
brew install llvm lld make dtc python3
pip3 install sdfgen==0.23.1
```

If you get `error: externally-managed-environment`
when installing via pip, instead run:
```sh
# sdfgen is an isolated package and does not depend on anything
# else so it will not break any system packages.
pip3 install --break-system-packages sdfgen==0.23.1
```

#### Microkit SDK

For Apple Silicon:
```sh
wget https://github.com/seL4/microkit/releases/download/2.0.1/microkit-sdk-2.0.1-macos-aarch64.tar.gz
tar xf microkit-sdk-2.0.1-macos-aarch64.tar.gz
```

For Intel:
```sh
wget https://github.com/seL4/microkit/releases/download/2.0.1/microkit-sdk-2.0.1-macos-x86-64.tar.gz
tar xf microkit-sdk-2.0.1-macos-x86-64.tar.gz
```

### Nix

There is a Nix flake available in the repository, so you can get a development shell via:
```sh
nix develop
```

Note that this will set the `MICROKIT_SDK` environment variable to the SDK path, you do not
need to download the Microkit SDK manually.

## Examples

You can find examples making use of the sDDF in the `examples/` directory. Each example has its
own README for how to build and run it.

Note that some examples may have dependencies in addition to the ones listed in this README.

## Developing

If you intend to work on the sDDF, please look at the documentation in
[docs/developing.md](docs/developing.md).
