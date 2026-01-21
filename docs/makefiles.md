<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->
The GNUmake build system
================================

The build system is structured so that each board, toolchain, driver and
component has a 'snippet' -- a fragment of a Makefile -- that can be included in
a project Makefile.

In the examples directories you will see how they are used.

There is a Makefile, that sets up a directory for the example to be built in.
It copies a per-example Makefile into the build directory, then invokes Make
recursively inside the build directory.

The per-example Makefile sets up some variables, then includes
`tools/Make/board/common.mk` which in turn includes board and tool-chain
specific snippets.  These set up variables for controlling the build --- see the
list of variables below.  In particular, the names of directories holding the
drivers for the board are put into specific variables.  The project directory
then can `include` the drivers it needs, using these variables.

Variables
---------

### Set by top-level Makefile, command line, or environment ###

| Variable           | Purpose                                |
|:-------------------|:---------------------------------------|
| `BUILD`            | Name of Build directory                |
| `TOOLCHAIN`        | Either `clang` or `gcc`                |
| `MICROKIT_BOARD`   | Board to build for                     |
| `MICROKIT_SDK`     | Directory containing the SDK           |
| `SUPPORTED_BOARDS` | List of boards that are known to work  |
| `MICROKIT_CONFIG`  | `benchmark`, `debug`, or `release`     |
| `SDDF`             | Name of top level directory containing |
|                    | the SDDF source tree                   |


### Set by Board snippet ###
All the `...DRIV_DIR` variables give the name relative to
`${SDDF}/drivers/`_deviceclass_

| Variable         | Purpose                                            |
|:-----------------|:---------------------------------------------------|
| `PLATFORM`       | Internal use: the name of the 'platform'           |
| `CPU`            | For aarch64 only: the CPU variant to optimise for  |
| `BLK_DRIV_DIR`   | Directory containing the block driver              |
| `I2C_DRIV_DIR`   | Directory containing the I2C host driver           |
| `NET_DRIV_DIR`   | First ethernet driver                              |
| `ETH_DRIV_DIR1`  | Second ethernet driver                             |
| `ETH_DRIV`       | Name of elf file for first ethernet driver         |
| `ETH_DRIV1`      | Name of elf file for second ethernet driver        |
| `TIMER_DRIV_DIR` | Directory containing timer driver                  |
| `UART_DRIV_DIR`  | Directory containing the asynchronous serial driver |


### Set by `common.mk` ###

| Variable        | Purpose                                     |
|:----------------|:--------------------------------------------|
| `BOARD_DIR`     | Directory inside the Microkit SDK for       |
|                 | the board and `MICROKIT_CONFIG`             |
| `MICROKIT_TOOL` | Tool from the Microkit                      |
| `DTS`           | Device tree source for the board            |
| `DTB`           | Device tree binary name                     |
| `DTC`           | Device tree compiler                        |
| `PYTHON`        | Name of python interpreter to use           |
| `LDFLAGS`       | A start at the board-specific flags to `ld` |





`common.mk` also generates a file that is named by the hash of toolchain, board,
and `MICROKIT_SDK`, and adds its name to the `.EXTRA_PREREQS` variable.  This
means that if any of these things change, everything will be rebuilt.

### Set by the Toolchain make snippet ###

The Toolchain make snippet (for cang or gcc) sets the usual compiler names
(`CC`, `LD`, `RANLIB` etc.

In addition it sets `ARCH` to either `riscv64` or `aarch64`; and sets up the
CFLAGS to build and optimise for the board's CPU.

CFLAGS includes an OPTIMISATION variable; this is set by default to `-O3 -g`,
but can be overridden on the Make command line.

### Driver Make Snippets ###

Each driver make snippet (except for Ethernet) generates an ELF file called
_class_`driver.elf`.  To build the elf file, include the snippet in your
Makefile and then make sure your final target depends on the ELF file.

Ethernet is special.  Some boards have more than one ethernet device that need
different drivers.  If your project needs only one ethernet device, you can
depend on `eth_driver.elf`; it will be built from whatever is the first ethernet
device defined in the board file.

If you need more than one ethernet device, you will need to use the _real_ name
of the ethernet drivers you need.  So for the imx8mp series of boards, the first
ethernet device uses `eth_driver_imx.elf` and the second (if needed) uses
`eth_driver_dwmac-5.10a.elf`; these are the ones you need to deal with in your
Makefile.
