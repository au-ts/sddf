# Revision history for sDDF

## Release 0.7.0

### Features

* Update to Microkit 2.3.0, including seL4 16.0.0
* Baseline x86_64 support has been added
* SMP support has been added
* New 'VSwitch' feature for the networking component
* Model checking of the serial queues under the weak memory model using [GenMC](
  https://plv.mpi-sws.org/genmc).

New board support:

* AArch64

  * Raspberry Pi 4 (serial/timer/network)
  * ZynqMP (ZCU102, ZCU106, Kria K26) (serial/timer/network)
  * Rock3b support (serial/timer/network)

* RISC-V

  * Star64 (serial/timer/network)
  * Cheshire support (serial)
  * [Serengeti] support (serial/timer/i2c)
  * Hifive P550 (serial)

* x86_64

  * Microkit `x86_64_generic` and `x86_64_generic_vtx` platforms (serial/timer/network/blk)


Breaking changes:

* The Zig build system has been removed as it duplicated the effort we spent
  on the Make build system.
* The minimum version of Python is now 3.10.
* Required 'sdfgen' version has been updated to v35
* Makefile toolchain details have been abstracted to `tools/make` to reduce
  duplication.
* I²C protocol has been rewritten

[Serengeti]: https://github.com/au-ts/serengeti

#### Block

* Support GPT partition schemes, not just MSDOS (MBR) partitions
* IMX MMC driver supports 25MHz "Default Speed" operation
* Add `blk_storage_set_ready` helper for driver internals
* Example now depends on the Serial subsystem so it works in release mode
* Support for the 'x86_64_generic' Microkit platform in QEMU (via VirtIO)
* Experimental support for NVMe on AArch64/Riscv64/x86_64 platforms
  * Note: x86_64 NVMe does not work with Microkit 2.3.0 as sDDF does not
    declare the appropriate IOMMU regions in the Microkit system. It does work
    on Microkit 2.2.0, which disables the IOMMU completely.
* Our `mkvirtdisk` script for QEMU systems supports creating `ext4` partitions
  as well. It is run when simulating examples on QEMU.

#### I²C

* Protocol has been completed refactored in [PR 509](https://github.com/au-ts/sddf/pull/509)
  and the [Design RFC](https://github.com/au-ts/sddf/issues/486).
* Example now depends on the Serial subsystem so it works in release mode
* There are now blocking and non-blocking 'libi2c' APIs.
* Support for Serengeti with `eth,i2c` (based on OpenTitan I²C)
* New example: "I²C bus scan" which lists I²C addresses present on the bus
* New example: "INA219" that reads current/voltage/power from an INA219 peripheral,
  currently targeted at the bus addresses on the Digilent Genesys 2 FPGA dev
  board that runs Serengeti or Cheshire.

#### Network

* Support for the Pine64 Star64 board using the `dwmac-5.10a` driver.
* Update the copy component to drop active Rx DMA buffers if client's free queue is empty
* Improve the echo server example's TCP echo socket
* Add features to lib sDDF lwip to allow the user to intercept packets before
  they are passed to the network subsystem (used by the firewall)
* Support multiple ethernet drivers for the same board by producing alternate
  ELF files for the driver
* Support for the [COMPULAB IOT-GATE-iMX8](
  https://www.compulab.com/products/iot-gateways/iot-gate-imx8-industrial-arm-iot-gateway/)
  boards.
* Address Conflict Detection (DHCP ACD) is disabled on QEMU platforms
  as this significantly reduces DHCP time.
* Various driver improvements to increase performance;
    * Use more appropriate AHB PBL (programmable burst length) value on various platforms
    * Use store-and-forward for Meson
    * Use hardware checksum offload on OdroidC4
* Support for an SMP configuration of the 'echo server' example
* `lib_sddf_lwip` helper functions now use common `sddf_lwip` prefix.
* Support for the VirtIO driver on PCI has been added
* Support for the 'x86_64_generic' Microkit platform in QEMU (via VirtIO)
* Support for Rock3b with `snps-dwmac-4.20a`.
* Support for Raspberry Pi4 with `brcm,bcm2711-genet-v5`
* New VSwitch components, [documented here](https://github.com/au-ts/sddf/blob/main/docs/network/vswitch.md).
* Support for the ZynqMP (ZCU102/Kria k26) platforms with `zynqmp-gem`
* Spin PROMELA models for signalling protocol verification now have documentation
  and the models are checked in CI.

#### Serial

* New `ns16550a` serial driver.
* QEMU RISC-V now defaults to using an `ns16550a` driver instead of the VirtIO
  console driver. Change the `UART_DRIV_DIR` in `tools/make/board/qemu_virt_riscv64.mk`
  if you wish to use VirtIO console instead.
* Star64 platform support via ns16550a.
* Cheshire/Serengeti platform support via ns16550a.
* ZynqMP (ZCU102/ZCU106/KRIA26) platform support for `xlnx,zynqmp-uart`
* Raspberry Pi 4B support via ns16550a.
* Hifive P550 (ESWIN 7700X) support via ns16550a.
* x86_64 support via the pc99 driver (ns16550 but over IO port)
* Rock3b support via ns16550a.

#### Timer

* Support more than 6 clients using the timer subsystem at one time.
* Add universal time conversion API which has a formal (Z3 SMT) proof of
  correctness, for conversion between time and ticks without overflow.

* Support for x86_64 platforms using the HPET timer.
  * Then a new TSC 'fastpath' timer read when supported via hardware.
* Support for the ZynqMP `cdns,ttc` driver.
* Support for the BCM2835 (Raspberry Pi 4B) `brcm-bcm2835-system-timer`.
* Support the Serengeti APB timer `pulp,apb_timer`
* Support for the Rock3b using `rockchip,rk3568-timer`.

#### Miscellaneous

* Vendored 'libco' implemented now supports RISC-V (64-bit) as well
* Remove support for `cache_invalidate` as it is always faster to use
  userland `cache_clean_and_invalidate` instead (invalidate goes via kernel)
* We include a custom libc in sDDF that can be externally overridden with a
  'true' libc, which has from-source builds of optimised `memcpy` and other
  features expecting by a freestanding compiler.
* 'Echo server' example works in SMP mode and can be benchmarked on other
  architectures, although cycle counts are not emitted for x86.
* Examples are run weekly on hardware and on every PR in QEMU using a new
  [testing framework](https://github.com/au-ts/sddf/tree/main/ci).
* The sDDF design document is now built and included as part of the repo.
* There is new developer documentation in the `docs/` folder.
* VirtIO drivers can now work on both PCIe and MMIO transport layers
* Add missing `memmove()` function for AArch64 to our minimal libc
* Add `ROUND_DOWN` macro to `util.h`.
* 'Agnostic' support added; so drivers can be used on top of non-Microkit systems
  such as [Djawula](https://trustworthy.systems/projects/Djawula)
* Most QEMU/simulated boards specified fixed VirtIO MMIO buses or PCI addresses
  as QEMU will often change the values between different versions.
* Implemented a ['memory barrier API'](https://github.com/au-ts/sddf/issues/642)
* Echo Server benchmarks are run weekly in CI and their results are logged.
* Benchmark: Add support for build time choice of PMU events, more defined events & different defaults
* Toolchain: export a `CXX` variable in makefiles
* VirtIO: add option to skip PCI bus probing

### Bugfixes

* network/virtio: add appropriate memory barriers
* network/virtio: map hardware rings as cached, which fixes coherency issues
  when running on *real* AArch64 KVM.
* Bug fixes for 'bitarray', 'fsmalloc' and 'ialloc' libraries
* use /usr/bin/env instead of hardcoded shell paths
* echo_server: fix process script for benchmarking events
* echo_server: fixup duplicate uart_driver and virt_tx pds
* benchmark: added required memory barriers to synchronise pmu interactions
* drivers/tsc_hpet: serialise rdtsc
* Makefile dependency fix
* benchmark: Check for overflows during benchmarking
* ci: increase echo server DHCP timeout for RPi4B
* examples/timer: only print after setting a timeout
  Redues time drift when printing to the console is slow.
* timer/hpet: change IRQ and many bug fixes
* i2c/opentitan: Don't enqueue more reads than we have space for
  in the RX fifo
* i2c/opentitan: Don't use target-mode-only interrupts
* i2c/opentitan: fix issues from #680
* i2c/opentitan: removed fmt thresh IRQ to prevent hanging on simple reads.
* make: remove CHECK_FLAGS_BOARD_MD5 as common.mk appends already
* i2c/opentitan: fix log printing + misc fixes
* libco/rv64: addi -> addiw for unsigned XLEN add
* lib_sddf_lwip: add create modifier to ar invocations
* nvme: clamp queue depth to controller CAP.MQES
* nvme: add memory barriers to queue operations
* examples/i2c: only add GPIO/clock regions for Odroid-C4 I2C
* network/dwmac: dwmac: Don't use raw tail index - #656
* timer/hpet: add retain, used to section
* timer/arm: add retain, used to section
* serial/pc99: avoid device_resources section being optimised out
* Echo server: Explicitly use the latency-check ipbench client test
* Fix missing libc build dependencies
* blk: fix virt init for unexpected notifies
* virtio: specify blk,eth devices for qemu by hand
  This will make it more reliable when QEMU versions change.
* examples/blk: typo fix for VirtIO regs
* virtio/pci: cleanup/fixes for PCI metadata checking
* examples/timer: remove duplicate variable from meta.py
* lib_sddf_lwip: assert that the number of pbufs is >= the number of Rx buffers
* examples/echo_server: remove the pending tx pbufs from the echo server - drop packets instead
* lib_sddf_lwip: Notify the Tx virtualiser if there are no Tx free buffers available
* toolchain: use -O2. This fixes performance on RISC-V.
* examples/echo_server: Remove duplicate protection domain declarations
* serial: fix signalling protocol under smp
* examples/serial: Fix libsddf_util_debug dependency
* Function definitions in header files should be inline
* i2c/queues: fix memory barriers
* timer/bcm2835: fix spurious interrupts
* network/virtio: fix rx packet length read
* util/assert: prevent infinite recursion & a stack overflow when asserts are
  called during a previous assert.
* serial/ns16550a: do not set baud while busy
* network/dwmac: fix UB in `1 << 31` shifts by using `BIT(n)` macro.
* serial/virt: correctly implement the signalling protocol
* serial: enable TX FIFO available interrupts when waiting to send data
* timer/jh7110: fix large timeouts
* timer/meson: bugfix by acking IRQs on init
  * This was later migrated to be done for all drivers as part of Microkit
* network/dwmac: use the same MAC address as U-Boot does
* serial/ns16550a: read/write to registers appropriately, as many are read-to-clear
  but were used as if they were read-write registers
* serial/ns16550a: fix initial driver reset deleting previous serial output
* flake.nix: add various missing dependencies
* various drivers: use sddf_dprintf for log printing, which works in debug mode
* block/virtio: fix compile warning
* virtio: ack interrupts *before* handling responses
* block/virtio: fix debug print compile error
* timer/jh7110: prevent potential race in time reads
* network/dwmac: fix ethernet dwmac bug introduced by removing descriptor array
* network: prioritise handling tx IRQs over rx IRQs; this is more performant,
  see [issue #419](https://github.com/au-ts/sddf/issues/419).
* examples/echo_server: fix multi-threaded compilation by tracking deps correctly
* serial: don't service RX queues when RX is disabled
* block: Bugfixes for error conditions in the IMX MMC driver
* Fix `libco` `-Wnull-dereference` warnings on newer compilers

## Release 0.6.0

### General

* Move to Microkit 2.0.1.
* Better support for RISC-V platforms in general.
* Add initial documentation for developing a new sDDF driver for existing device
  classes.
* Add Nix flake for Nix users.
* On ARM, make better use of memory barriers when doing cache maintenance
  ([#348](https://github.com/au-ts/sddf/pull/348)). This significantly reduces
  utilisation in our networking and block benchmarking.

#### Metaprogram

One of the biggest changes in this release is moving all of our components to
get their configuration info to be auto-generated. Previously, much of this was
hard-coded which became difficult to maintain and did not scale.

The tooling alleviates some of the friction with putting a system together, but
is still experimental and undergoing active development.

In the example systems you will see a metaprogram that is responsbile for
declaring the system architecture and configuration of the system.

You can find how to use the tooling by exploring the [example
systems](https://github.com/au-ts/sddf/tree/0.6.0/examples) and reading the
[developer docs](https://github.com/au-ts/sddf/tree/0.6.0/docs/developing.md).

#### Support for other seL4-based OSes

sDDF has been developed using the seL4 Microkit and so expects minimal wrappers
over seL4 system calls which Microkit provides.

Much of the sDDF code itself is generic and does not rely on a specific seL4 OS
and so we have begun transitioning our sub-systems to be able to work on
different seL4-based OSes. This is primarily motivated by another Trustworthy
Systems project, the [Secure Multiserver Operating System
(SMOS)](https://trustworthy.systems/projects/smos/) but also making sDDF
available to others in the seL4 community.

Not all of sDDF has undergone this transition, but we have made certain device
clases and drivers 'agnostic' such as serial, timer, and network. For example,
the [echo server
system](https://github.com/au-ts/sddf/tree/0.6.0/examples/echo_server) works in
a SMOS environment (note that SMOS is not open-source at this time).

### Audio

* Use 'capacity' instead of 'size' when referring to the maximum number of
  entries in a given queue.

### Block

* Add block example that shows off basic usage of the block protocol.
* Add initial i.MX8 uSDHC driver.
    * Note that this is a fairly experimental driver and known not to perform
      well. See [the tracking issue](https://github.com/au-ts/sddf/issues/187)
      for more details.
* Add virtIO driver for using virtual disks from QEMU.
* Fix bugs with certain edge cases in virtualiser (e.g invalid requests).
* Improve error codes given in response status.

### GPU

This release adds an initial design and implementation for 2D graphics.

This device class is very experimental. We have an initial virtIO GPU driver and
example system for use with QEMU but there are many open design questions to be
resolved.

### I<sup>2</sup>C

* Various fixes to the Meson I2C host driver.
* Improvements for the PN532 card-reader driver.
* Add I2C driver for the DS3231 RTC device.

### Network

* Add Synposis DWMAC (5.10a) ethernet driver.
* Add board support in echo server example for:
    * i.MX8MP-EVK
    * Odroid-C2
* Introduce `lib_sddf_lwip` library to make it easier to write networking
  clients when using lwIP.
* Use 'capacity' instead of 'size' when referring to the maximum number of
  entries in a given queue.
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
    * In the future we will have 'clk' drivers so this should make things less
      confusing.
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
    * Previously a development version of Microkit was used, now we use an
      official release for everything.
* Add QEMU support to the timer and echo server examples.
* Remove dependency on a full libc, all the provided components use our own
  utility functions now.
* Transition to a modular 'Makefile snippets' build system structure to simplify
  the composition of sDDF components.
* Introduce snippets for the Zig build system, as an alternative to Make.
    * Instructions for using the Zig build system can be found in each example's
      README.
    * No components are solely built with Zig, the primary build system is still
      Make.
* Introduce configurable printf logging for debug versus release mode, making it
  easier to have some components continue logging to the serial in release mode.

### Block

* Move the capacity of the shared queue out of shared memory and into the queue
  handles. This prevents malicious clients from messing with the queue size and
  potentially causing the virtualiser or other trusted components to
  crash/misbehave.
* Introduce a config header to enable the system designer to have a variable
  amount of clients, previously it was all hard-coded.
    * It should be noted that we are working on tooling to automate this process
      and these configs are likely to significantly change by the next release.
* Change block virtualiser to use offsets when interfacing with clients and DMA
  physical addresses when interfacing with the driver.
    * This makes the block system consistent with the networking system in how
      it handles client-to-driver address translation.
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
* Fix caching operations in RX virtualiser, previously this would lead to issues
  with TCP traffic.
* Various bug fixes in the Amlogic ethernet driver.
* Fixes and changes for improved TCP performance.

### Serial

* Redesign the entire sub-system.
    * The serial device class was previously following the network design which
      was not an ideal design for serial devices. This new design is intended to
      be used for character-by-character devices. DMA capable serial devices
      will have a separate design, more aligned with the design of our other DMA
      capable devices such as ethernet and block.
    * Various bugs were fixed and so individual drivers as well as the system as
      a whole should be more stable.
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
* Various cleanup/refactoring of all the drivers to simplify their
  implementation and fix bugs.
