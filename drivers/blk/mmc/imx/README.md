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
- Supports Version 2 SD Cards (SDSC, SDHC, SDXC, SDUC) operating at 3.3V / $f_{OD}$ (400kHz).

## Not Implemented
- Voltage Negotiation (anything but 3.3V)
- Version 1 SD cards (the initialisation flow)
- Version 2 SDSC / SDXC cards (card capacity calculation)
- Higher speed operation (even Default Speed / 25 MHz ($f_{PP}$)) and DDR
- Setting as RO when write protect is set on the SD card
- Clock setup (currently inherits 150MHz clock from U-Boot)
- Pinmux setup (again, inherits from U-Boot)
- Timeouts as required by some SD commands
- Card detection
