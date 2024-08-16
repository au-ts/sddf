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

## Building and running examples

You can find examples making use of the sDDF in the `examples/` directory. Each example has its
own README for how to build and run it.

## Dependencies

### Toolchain

Any C toolchain should work but most testing and experimentation is currently performed with
the `aarch64-none-elf` GCC toolchain distributed by ARM. You can download it from
[here](https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads).

The specific version used for testing is:
`aarch64-none-elf-gcc (GNU Toolchain for the A-profile Architecture 10.2-2020.11 (arm-10.16)) 10.2.1 20201103`.

### Microkit SDK

The sDDF is built using the [seL4 Microkit](https://github.com/seL4/microkit) (version 1.4.1).

You can download version 1.4.1 of Microkit SDK from
[here](https://github.com/seL4/microkit/releases/tag/1.4.1).

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
