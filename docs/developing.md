<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->
# Developing sDDF

The majority of the development of sDDF is done by Trustworthy Systems
in Sydney, Australia by various students and engineers. This document serves
as a guide for them but also for anyone wanting to develop a driver or new
device class for sDDF.

Please feel free to open an issue on GitHub if there is something missing or
something is not clear.

## Examples

For each device class in sDDF, we have an example system in `examples/` to
show how to use the device class as a client as well as how to hook everything
up.

### The metaprogram

Common to each example is a 'metaprogram'. It is responsible for generating
certain artefacts that each sDDF component is expecting as well as the Microkit
System Description File (SDF).

Previously, there was no metaprogram and we wrote the SDF by hand and used
C headers to encode the sDDF specific configuration. This did not scale well
and was error prone and so we have been working on tooling to decrease the friction
when building more complicated systems.

The metaprogram is specific to each example system, it makes use of the
[sdfgen](https://github.com/au-ts/microkit_sdf_gen) tooling to auto-generate the
artefacts mentioned above.

The sdfgen tooling allows users to describe systems in a higher level without
needing to focus on tedious details that are necessary to put a system together.
It provides an API for doing this that we invoke in our metaprogram to build up
the system by adding the required protection domains, memory regions, and sDDF
sub-systems.

sdfgen provides a C API as well as a Python package. For the purpose of ease of
experimentation, the metaprograms in the example systems are a Python script but
what language you use is up to you.

You can find more details in the [repository](https://github.com/au-ts/microkit_sdf_gen)
and an API reference for the Python package [here](https://au-ts.github.io/microkit_sdf_gen/).

### Adding a new board

The first step is to figure out whether the devices you want to make use of
with your board have corresponding drivers in sDDF already.

For ARM and RISC-V, we target specific boards rather than a particular SoC
and so even if sDDF already has the drivers required for your board, there is
still a bit of work needed to add support.

The first step is to get the Device Tree and puts it in the `dts/` directory
of sDDF. You can then start either writing the new drivers for devices you want
to use, or modify the examples to add your board.

## Adding a new driver

If you are adding a driver for an *existing* device class, you'll need to add
the following:
* the configuration file
* the driver code itself
* integration into the build system
* integration into an example system

### Writing the driver

All drivers are in `drivers/`, each device class has its own sub-directory and
each kind of driver has it's own sub-directory within that.

For example, the i.MX8 UART driver would go under `drivers/serial/imx/`. The
directory for the driver typically refers to its manufacturer or the family
of devices the particular driver is written for.

For writing the actual driver code, it is best to first understand how the device
class works within sDDF, by reading the
[design document](https://trustworthy.systems/projects/drivers/sddf-design.pdf).

After that, you should have a high-level understanding of what the responsibility
of the driver is for your device class. For specifics, it is best to study the
existing drivers and follow their layout. Generally, the drivers within the same
device class will have the same flow and structure with differences in initialisation,
interrupt handling, register access, etc.

To understand the how the driver should interact with the device there are a couple
different avenues:
* The technical reference manual for the SoC or device.
    * Unfortunately sometimes this either does not contain enough information to
      write a driver or is not publicly available.
* Linux source code
* U-Boot source code.
    * Note that U-Boot drivers are not interrupt driven while all sDDF drivers are.
* Manufacturer provided SDKs or reference drivers.

#### Finding the Linux or U-Boot driver

To find the driver for your device in Linux or U-Boot, the easiest way to is to first
find the compatible string. This will be in the Device Tree for your particular board.

To find the Device Tree look at the Linux source or seL4.

With the compatible string, you can now search for all mentions of it in the Linux or
U-Boot source. You should find at least one source file that contains it, typically
this is the source file for most if not all of the driver.

### Configuration file format

All fields are required unless otherwise specified as optional.

* `name`: Unique identifier for the driver.
* `compatible`: List of Device Tree compatible strings that
                the driver is known to work with.
* `resources`:
    * `regions`: List of objects describing each region needed by the driver.
        * `name`: Unique identifier for the region.
        * `size` (optional): Size of region.
                             Must be page-aligned.
                             If `dt_index` is not provided this is required.
        * `dt_index` (optional): Index of corresponding region in the Device Tree node.
                                 A normal memory region will be created if this is not
                                 provided.
        * `perms` (optional): permissions associated with the mapping of the region.
                              Defaults to "rw".
                              "r" is read access.
                              "w" is write access.
                              "x" is executable.
    * `irqs`: List of objects describing each interrupt needed by the driver.
       * `dt_index`: Index of corresponding interrupt in the "interrupts" property
                     of the Device Tree node for the device.

#### Example

Below is what the configuration file looks like for the ARM PL011 UART device driver.

```json
{
    "compatible": [
        "arm,pl011"
    ],
    "resources": {
        "regions": [
            {
                "name": "regs",
                "size": 4096,
                "dt_index": 0
            }
        ],
        "irqs": [
            {
                "dt_index": 0
            }
        ]
    }
}
```

We specify a list of Device Tree compatible strings, in this case it is just
`arm,pl011`.

We then specify any device-specific resources the driver needs. In this case
we need an MMIO region for the device registers. We give it a name, the size
of the region the driver expects, and the index into the `reg` property of
the Device Tree node for the device.

```dts
    pl011@9000000 {
        clock-names = "uartclk", "apb_pclk";
        clocks = <0x8000 0x8000>;
        interrupts = <0x00 0x01 0x04>;
        reg = <0x00 0x9000000 0x00 0x1000>;
        compatible = "arm,pl011", "arm,primecell";
    };
```

In this case there's only one IRQ and one memory region associated with the device,
so `dt_index` has to be zero but there are cases where the driver only needs a subset
of what is available.

The same applies for interrupts.

These resources then become available at run-time by the driver and are used via the
`device_resources_t` structure. For examples of using it is best to look at other driver
code.

### Build system

sDDF works with two build systems, GNU Make and Zig.

Make is the primary build-system, if you are unfamiliar with Zig you won't lose out
on anything. We do however aim to keep both the Makefiles and Zig builds capable of
building all the parts of sDDF.

There is a snippet system for the Makefiles and so each driver will have its own
`.mk` file for building itself. You can base your drivers snippet on other ones within
the same device class.

## Adding a new device class

Adding a new device class is a significant task as it requires a strong understanding
of the sDDF principles as well as the device class in order to have a good design.

If you are an outside contributor and are interested in adding a new device class,
please contact the developers by opening an issue on the GitHub repository.
