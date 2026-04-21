<!--
    Copyright 2026, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# I²C example: INA219

This example makes use of the [Texas Instruments INA219](
https://www.ti.com/lit/ds/symlink/ina219.pdf) current/power monitor chip.

It is tested to run on our [Serengeti RISC-V SoC](https://github.com/au-ts/serengeti),
which is a soft-core running on the [Digilent Genesys 2 FPGA Board](
https://digilent.com/reference/_media/reference/programmable-logic/genesys-2/genesys2_rm.pdf),
which has INA219 ICs connected to the main power rails of the FPGA.

It should also run on any of our other I²C platforms, provided that you adjust
the I²C address and the constants for the configuration & calibration registers
that are correct for your board.

## Building

To build, run the following command:

```sh
$ make MICROKIT_SDK=/path/to/sdk MICROKIT_BOARD=serengeti -j$(nproc)
```

The final bootable image will be in `build/loader.img`.

## Running

The example first claims the I²C addresses, and then sits in an infinite loop.
Every 5s it performs an I²C write-read request for the bus voltage, current,
and power measurements. You should see the following output in debug mode:

```
Booting all finished, dropped to user space
INFO  [sel4_capdl_initializer::initialize] Starting CapDL initializer
INFO  [sel4_capdl_initializer::initialize] Starting threads
MON|INFO: Microkit Monitor started!
MON|INFO: PD 'timer_driver' is now passive!
INA219|INFO: Measurement completed!
INA219|INFO:    Bus voltage = 3.262117V
INA219|INFO:    Current = 1072
INA219|INFO:    Power= 179
INA219|INFO: Measurement completed!
INA219|INFO:    Bus voltage = 3.262117V
INA219|INFO:    Current = 1072
INA219|INFO:    Power= 179
INA219|INFO: Measurement completed!
INA219|INFO:    Bus voltage = 3.262117V
INA219|INFO:    Current = 1072
INA219|INFO:    Power= 179
INA219|INFO: Measurement completed!
INA219|INFO:    Bus voltage = 3.262117V
INA219|INFO:    Current = 1072
INA219|INFO:    Power= 179
INA219|INFO: Measurement completed!
INA219|INFO:    Bus voltage = 3.262117V
INA219|INFO:    Current = 1072
INA219|INFO:    Power= 179
```
