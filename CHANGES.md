# Revision history for sDDF

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
