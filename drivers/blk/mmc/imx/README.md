<!--
    Copyright 2024, UNSW
    SPDX-License-Identifier: CC-BY-SA-4.0
-->

# uSDHC iMX8 Driver

This is a driver for the MaaXBoard SD host controller, based on the following documents:

- i.MX 8M Dual/8M QuadLite/8M Quad Applications Processors Reference Manual
  Document Number: IMX8MDQLQRM, Rev 3.1, 06/2021.
  https://www.nxp.com/webapp/Download?colCode=IMX8MDQLQRM
- SD Specifications Part 1 Physical Layer Simplified Specification.
  Version 9.10, Dec. 2023.
  https://www.sdcard.org/downloads/pls/
- SD Specifications Part A2 SD Host Controller Simplified Specification.
  Version 4.20, July 2018.
  https://www.sdcard.org/downloads/pls/

## Implemented
- IRQ & DMA based driver
- Supports 3.3V operation of Version 2 SDHC cards (4GiB–32GiB) at $f_{OD}$ (400kHz).

## Not Implemented
- Voltage Negotiation (anything but 3.3V)
- Version 1 SD cards (the initialisation flow)
- Version 2 SDSC / SDXC cards (only because I haven't implemented support for calculating card capacity)
- Higher speed operation (even Default Speed / 25 MHz ($f_{PP}$)) and DDR
- Setting as RO when write protect is set on the SD card
- Clock setup (currently inherits 150MHz clock from U-Boot)
- Pinmux setup (again, inherits from U-Boot)
- Timeouts as required by various commands & a lot of error cases
- Card detect on the MaaXboard doesn't seem to work (even in U-Boot/Linux)
