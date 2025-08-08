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

Before writing a new sDDF device driver, it is highly recommended to first gain
an understanding of the design principles behind the sDDF. All sDDF components,
data structures and communication mechanisms are implemented to adhere to these
principles, and consequently have a great deal in common. This is important
whether the class of the new device driver exists or not, as non-adherence may
cause difficulty when trying to utilise the new driver in other sDDF systems.

The [sDDF design document](https://trustworthy.systems/projects/drivers/sddf-design.pdf)
explains these principles and interfaces on a more abstract level and discusses
why they were chosen.

### Creations and modifications needed

If you are adding a driver for an *existing* device class, you'll need to add
the following:

* the driver configuration file
* the driver code itself
* integration into the build system
* integration into an example system

If you are adding a driver for a device class that does not exist, see the
section [on adding a new device class](#Adding-a-new-device-class).

### Existing components and drivers

Existing virtualiser components can be found in the corresponding
`[class]/components` directories. sDDF queue libraries can be found in
`include/sddf/[class]` directories.

All drivers are in `drivers/`, each device class has its own sub-directory and
each kind of driver has it's own sub-directory within that.

For example, the i.MX8 UART driver would go under `drivers/serial/imx/`. The
directory for the driver typically refers to its manufacturer or the family of
devices the particular driver is written for.

### Writing the driver

Writing a driver for sDDF typically involves three largely independent tasks:
* Initialising the driver and device data structures, and configuring the
  device. These tasks are performed in the `init` function
* Writing sDDF interfacing code to communicate with virtualisers
* Writing device interfacing code to create a device agnostic interface for the
  virtualisers

#### Interface

All sDDF drivers are event driven, and share a lot of similarities. Once
initialisation has been completed, a driver will only be awoken to respond to
signals from virtualisers and IRQs from the device. These are typically
triggered by only a handful of different events, and each will require a
specific handling function.

Each event indicates that data or buffers are available to be passed between the
device and virtualiser, the only differences being what type of data or buffer,
and which direction it needs to be passed. This dictates which sDDF queue each
handling function will process, and whether data needs to be enqueued or
dequeued from the queue. Consequently, each event handler has a very similar
structure, and the most difficult part of writing the code will be interacting
with the device.

sDDF event handling functions are typically named '[tx|rx]_[provide|return]',
where `tx` and `rx` correspond to transmission and reception, `provide`
corresponds to when data or buffers are passed towards the driver, and `return`
corresponds to when data or buffers are passed towards a client. The naming
convention is generally based on how the hardware works, hence `rx` and `tx`
for serial and networking. Other device classes, such as block, use `request`
and `response` since that maps onto the hardware better.

If the driver is of a pre-existing device class, an existing driver can be used
as a scaffold. You will find that there are very few if any changes that will
need to be made to the sDDF component of the initialisation code, the event
handling loop constraints and sDDF queue interactions. In the case of a new
device class, a similar class can also serve as a helpful scaffold.

#### Signalling protocol

The most dominant protocol used by sDDF components to communicate and share data
for all device classes is a combination of asynchronous notifications (e.g
`microkit_notify`) and shared memory (e.g data regions and/or queue regions).
Since components are event-based, when data has been made available to begin
processing the producer of this data is typically required to notify the
consumer of the data to ensure the consumer is scheduled. In some cases it is
also necessary for the consumer of the data to notify the producer if more space
has become available.

Since our systems contain large numbers of components handling multiple
independent events, components often incidentally become aware of events which
they were not explicitly notified for. Also, components may require more than
one event to occur before further progress can be made (e.g. one queue to become
non-empty and another to become non-full). Thus, if components notify their
neighbours unconditionally when progress is made, this can often result in the
receiver being scheduled unnecessarily without making further progress.

For device classes where these *unnecessary notifications* put too much of a
strain on the overall utilisation of the system (i.e. networking), the sDDF
utilises a *signalling protocol*. The signalling protocol allows producers and
consumers to communicate more preciesly about when they require a signal after
progress has been made. For some sub-systems, in some directions of
communication, components will only notify their neighbour when work has been
completed if a shared flag has been set.

However, utilising a flag in shared memory which is concurrently written to and
read from can result in deadlocks if care is not taken. To avoid this, a
model-checked signalling protocol was developed. This signalling protocol is
currently implemented in the network and serial subsystem. It involves a check
of a shared flag before a notifying:

```c
    if (packets_transferred && net_require_signal_active(&rx_queue)) {
        net_cancel_signal_active(&rx_queue);
        microkit_notify(config.virt_rx.id);
    }
```

as well as a less intuitive extra "double-check" before terminating a processing
loop. This prevents a component from failing to to process available data due to
a missed notification. This situation can occur if a neighbour checks the
component's flag before the component has had the chance to reset it (see
deadlock condition), but after it has terminated processing the queue:

```c
    bool reprocess = true;
    while (reprocess) {
        while (!(hw_ring_full(&tx)) && !net_queue_empty_active(&tx_queue)) {
            ... *process queues* ...
        }

        <-- deadlock condition -->

        net_request_signal_active(&tx_queue);
        reprocess = false;

        if (!hw_ring_full(&tx) && !net_queue_empty_active(&tx_queue)) {
            net_cancel_signal_active(&tx_queue);
            reprocess = true;
        }
    }
```

When writing a driver for these subsystems, care must be taken to ensure the
driver's event handling functions adhere to this protocol, and don't introduce
the possibility of deadlock. If the scaffold of the pre-existing driver's event
handling functions is unchanged, then this should not be a risk.

#### Interfacing with the device

Differences between drivers of the same device class typically boil down to
device initialisation (utilising different available features of different
devices), interrupt enabling and handling, register access, device specified
data structures and required memory regions.

To understand the how the driver should interact with the device there are a couple
different avenues:

* The technical reference manual for the SoC or device.
    * Unfortunately sometimes this either does not contain enough information to
      write a driver or is not publicly available.
* Linux source code
* U-Boot source code.
    * Note that U-Boot drivers are not interrupt driven while all sDDF drivers are.
* Manufacturer provided SDKs or reference drivers.

#### Code

Below is a list of things that should be in each driver regardless of device class:

* Each IRQ used by the driver must be acked during initialisation in-case there
  were undelivered IRQs from the time the IRQ is registered with seL4 and the driver
  starts.

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

When creating a new device class, you'll additionally need to create
the supporting infrastructure as well:
* *virtualiser* protection domains to perform security operations as well as
  client and data management tasks
* an sDDF queue library containing the queue data structure and helper functions
  used to pass data and buffers between drivers, virtualisers and clients
* an sdfgen module allowing the new sub-system to be seamlessly added to systems

Creating a new device class module for sdfgen is an involved task, and will
require encoding into the tool all the information that is needed for the
sub-system to be automatically generated. This includes:
* necessary protection domains (driver, virtualisers)
* memory regions and channels required for protection domains to use the
  corresponding queue library
* how virtualisers should organise their clients
* the configuration options available for the system (memory region sizes,
  protection domain priorities, client multiplexing options, data processing
  options, etc)
