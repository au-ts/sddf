# Revision history for sDDF

## Release 0.6.0

### General

* Move to Microkit 2.0.1.
* Better support for RISC-V platforms in general.
* Add initial documentation for developing a new sDDF driver for
  existing device classes.
* Add Nix flake for Nix users.
* On ARM, make better use of memory barriers when doing cache maintenance
  ([#348](https://github.com/au-ts/sddf/pull/348)).
  This significantly reduces utilisation in our networking and block benchmarking.

#### Metaprogram

One of the biggest changes in this release is moving all of our components
to get their configuration info to be auto-generated. Previously, much of this
was hard-coded which became difficult to maintain and did not scale.

The tooling alleviates some of the friction with putting a system together, but
is still experimental and undergoing active development.

In the example systems you will see a metaprogram that is responsbile for declaring
the system architecture and configuration of the system.

You can find how to use the tooling by exploring the [example systems](https://github.com/au-ts/sddf/tree/0.6.0/examples)
and reading the [developer docs](https://github.com/au-ts/sddf/tree/0.6.0/docs/developing.md).

#### Support for other seL4-based OSes

sDDF has been developed using the seL4 Microkit and so expects minimal wrappers
over seL4 system calls which Microkit provides.

Much of the sDDF code itself is generic and does not rely on a specific seL4 OS
and so we have begun transitioning our sub-systems to be able to work on different
seL4-based OSes. This is primarily motivated by another Trustworthy Systems
project, the [Secure Multiserver Operating System (SMOS)](https://trustworthy.systems/projects/smos/)
but also making sDDF available to others in the seL4 community.

Not all of sDDF has undergone this transition, but we have made certain device
clases and drivers 'agnostic' such as serial, timer, and network. For example, the
[echo server system](https://github.com/au-ts/sddf/tree/0.6.0/examples/echo_server) works
in a SMOS environment (note that SMOS is not open-source at this time).

### Audio

* Use 'capacity' instead of 'size' when referring to the maximum number
  of entries in a given queue.

### Block

* Add block example that shows off basic usage of the block protocol.
* Add initial i.MX8 uSDHC driver.
    * Note that this is a fairly experimental driver and known not to
      perform well. See [the tracking issue](https://github.com/au-ts/sddf/issues/187)
      for more details.
* Add virtIO driver for using virtual disks from QEMU.
* Fix bugs with certain edge cases in virtualiser (e.g invalid requests).
* Improve error codes given in response status.

### GPU

This release adds an initial design and implementation for 2D graphics.

This device class is very experimental. We have an initial virtIO
GPU driver and example system for use with QEMU but there are many
open design questions to be resolved.

### I<sup>2</sup>C

* Various fixes to the Meson I2C host driver.
* Improvements for the PN532 card-reader driver.
* Add I2C driver for the DS3231 RTC device.

### Network

* Add Synposis DWMAC (5.10a) ethernet driver.
* Add board support in echo server example for:
    * i.MX8MP-EVK
    * Odroid-C2
* Introduce `lib_sddf_lwip` library to make it easier to write networking clients
  when using lwIP.
* Use 'capacity' instead of 'size' when referring to the maximum number
  of entries in a given queue.
* Fix queue library to use entire capacity of queue.
    * A leftover artefact of a previous queue design meant that we were leaving
      one entry in the queue always empty when that is no longer necessary.
* Improve performance of virtIO network driver.
    * See [here](https://github.com/au-ts/sddf/issues/113) for more details.
* Fix drivers to use the entire hardware ring.

### Serial

* Add Synopsis DesignWare ABP UART driver.
* Add virtIO console driver.
* Add board support in serial example for:
    * i.MX8MP-EVK
    * i.MX8MQ-EVK
    * Odroid-C2
    * Pine64 Star64
    * QEMU virt RISC-V (64-bit)
* Various fixes and improvements to protocol and APIs.
* Rename `uart_driver.elf` to `serial_driver.elf` for consistency.

### Timer

* Rename timer drivers from 'clock' to 'timer'.
    * In the future we will have 'clk' drivers so this should make things less confusing.
* Add StarFive JH7110 timer driver.
* Add Google Goldfish RTC timer driver.
* Add board support in timer example for:
    * Odroid-C2
    * Pine64 Star64
    * QEMU virt RISC-V (64-bit)
* Fix counter overflow in ARM timer driver.

## Release 0.5.0

### General

* Move to Microkit 1.4.0.
    * Previously a development version of Microkit was used, now we use
      an official release for everything.
* Add QEMU support to the timer and echo server examples.
* Remove dependency on a full libc, all the provided components use our own
  utility functions now.
* Transition to a modular 'Makefile snippets' build system structure to
  simplify the composition of sDDF components.
* Introduce snippets for the Zig build system, as an alternative to Make.
    * Instructions for using the Zig build system can be found in each
      example's README.
    * No components are solely built with Zig, the primary build system is
      still Make.
* Introduce configurable printf logging for debug versus release mode, making
  it easier to have some components continue logging to the serial in release
  mode.

### Block

* Move the capacity of the shared queue out of shared memory
  and into the queue handles. This prevents malicious clients
  from messing with the queue size and potentially causing the
  virtualiser or other trusted components to crash/misbehave.
* Introduce a config header to enable the system designer to have a variable
  amount of clients, previously it was all hard-coded.
    * It should be noted that we are working on tooling to automate this process
      and these configs are likely to significantly change by the next release.
* Change block virtualiser to use offsets when interfacing with clients and DMA
  physical addresses when interfacing with the driver.
    * This makes the block system consistent with the networking system in how it
      handles client-to-driver address translation.
* Use 'capacity' instead of size in the shared queue library to avoid confusion.

### I2C

* Use 'capacity' instead of size in the shared queue library to avoid confusion.

### Network

* Add a virtIO network driver.
    * This allows us to have networking on QEMU making it easier to simulate
      non-trivial systems.
* Change RX virtualiser policy for broadcast packets.
    * Previously all broadcast packets would go to the ARP component, now the
      default policy is to forward broadcast packets to all clients.
    * We have only run into this becoming necessary so far when simulating our
      systems using QEMU since its internal DHCP server sends broadcast packets.
* Introduce a config header to enable the system designer to have a variable
  amount of clients, previously it was all hard-coded.
    * It should be noted that we are working on tooling to automate this process
      and these configs are likely to significantly change by the next release.
* Fix caching operations in RX virtualiser, previously this would lead to
  issues with TCP traffic.
* Various bug fixes in the Amlogic ethernet driver.
* Fixes and changes for improved TCP performance.

### Serial

* Redesign the entire sub-system.
    * The serial device class was previously following
      the network design which was not an ideal design for serial devices. This new
      design is intended to be used for character-by-character devices. DMA
      capable serial devices will have a separate design, more aligned with the design
      of our other DMA capable devices such as ethernet and block.
    * Various bugs were fixed and so individual drivers as well as the system
      as a whole should be more stable.
* Introduce a config header to enable the system designer to have a variable
  amount of clients, previously it was all hard-coded.
    * It should be noted that we are working on tooling to automate this process
      and these configs are likely to significantly change by the next release.

### Sound

This release adds the initial sound virtualiser and shared queue library.

We do not yet have any native sound drivers.

See the design document for the specification and more information.

### Timer

* Add a driver for the ARM architectural timer (necessary for QEMU on ARM).
* Various cleanup/refactoring of all the drivers to simplify their implementation
  and fix bugs.
