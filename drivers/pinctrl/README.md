<!--
    Copyright 2024, UNSW
    SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Pin control driver
Also known as pinmux driver

# Terminology
- Port: refers to an input or output line of a logic instance in the chip (e.g. UART, DDR, HDMI, I2C,...). For example, an I2C instance have SDA and SCL ports. Not to be confused with pad.
- Pad: refers to the physical pin on the chip package (example, ball for BGA packaged chips). 

# Overview
<!-- This paragraph is from Linux documentation -->
A chip contains a limited number of pads as it is not feasable to have a one-to-one mapping between all pads and ports. Hence, most of the pads have multiple signal options. I.e. a pad can be connected to one of multiple ports at a given point in time as appropriate for the intended use case. These signal-to-pin and pin-to-signal options are selected by the input-output multiplexer called pinmux. The pinmux is also used to configure other pin characteristics, such as drive strength, bias, etc...

Even though the pinmux parameters can be set dynamically at runtime, we restrict ourselves to settings that are set in the device tree at compile time and disallow any deviations from that. 

Before the pinmux driver is built, a Python script will read the target board's device tree source file, extracting all the pinmux settings and encodes them as binary values in an assembly file. Then the driver is built and linked with the pinmux data assembly file, creating a complete pinmux driver ELF image.

The pinmux driver must be exclusively run at the highest priority to ensure that it is the first PD initialised in the system. At `init()` time, the driver to read the encoded pinmux data and write it into the pinmux device. Other PD can access the pinmux device in a read-only manner via PPC into the driver. See `<sddf/pinctrl/client.h>` for more details.

# Usage
This driver can be used to test changes to the device tree source file, as it can overwrite U-Boot's or another bootloader's initialisation of the pinmux device.

Or it can be used as a pinmux emulator for a driver VM system.

# iMX8-* details
@billn FILL IN

# OdroidC4 details
@billn FILL IN
