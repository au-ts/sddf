<!--
    Copyright 2025, UNSW
    SPDX-License-Identifier: BSD-2-Clause
-->

# I<sup>2</sup>C sub-system

sDDF has support for I<sup>2</sup>C host controllers as well as certain
I<sup>2</sup>C devices.

For a list of the supported host controllers, see [../drivers.md](../drivers.md).

Below is a list of the devices supported:

* NXP PN532 card reader.
    * Testing was done with the
      [PN532 NFC RFID Module V3](https://www.nxp.com/docs/en/user-guide/141520.pdf).
    * The code was based an Arduino PN532 library found
      [here](https://github.com/elechouse/PN532/).
* Analog Devices DS3231 RTC.
    * Documentation can be found
      [here](https://www.analog.com/media/en/technical-documentation/data-sheets/ds3231.pdf).
