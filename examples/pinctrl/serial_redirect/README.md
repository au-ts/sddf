<!--
    Copyright 2024, UNSW
    SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Terminology
- Port: refers to an input or output line of a logic instance in the chip (e.g. UART, DDR, HDMI, I2C,...). For example, the I2C1 instance have a SDA and SCL ports. Not to be confused with pad.
- Pad: refers to the physical pin on the chip package (example, ball for BGA packaged chips). 

# Overview
The chip contains a limited number of pins, most of which have multiple signal options. These signal-to-pin and pin-to-signal options are selected by the input-output multiplexer called IOMUX. The IOMUX is also used to configure other pin characteristics, such as voltage level, drive strength, and hysteresis.

In other words, a pad can be switched/muxed between a subset of the chip's ports dynamically. For example, you can connect a SPI3_MOSI port onto a UART1_TX pad. However, not all pads can be muxed where it does not make sense to do so, e.g. HDMI, DDR, USB... and since the muxing is implemented in hardware, not all muxing path is possible, e.g. you can't connect a UART1_TX port onto a UART3_TX pad on the iMX8-* chips.

This driver implements a protocol that allow clients to communicate with the IOMUX controller. Before the driver object is built, there is a Python script that parses a Device Tree Source (DTS) file to extract all the correct mux register values and offsets to write to memory. This data is then patched into the driver's executable during the build steps.

The driver must be run at the highest exclusive priority to ensure it runs first where it will set up the IOMUX controller with all the values from the DTS.

# Pinmux client example

This is an example system demonstrating a client using the pinctrl driver to make the IOMUX controller on chip to redirect output of UART1_TX pad to different port of the chip.

# Building

Define the environment variable `MICROKIT_SDK`.

Then run `make MICROKIT_BOARD=$BOARD`. Where $BOARD can be one of `{maaxboard, imx8mq_evk, imx8mm_evk}`.

Finally boot the result image at `build/loader.img`.

# Output
You will see a bunch of output from the driver while it is initialising, that is the data from the device tree:
```
PINCTRL DRIVER|INFO: starting
PINCTRL DRIVER|INFO: nums of config is 171
PINCTRL DRIVER|INFO: data dump begin...one pin per line
PINCTRL DRIVER|INFO: mux reg: 0x44 = 0, input reg: 0x0 = 0, pad conf reg: 0x2ac = 25. PINCTRL DRIVER|INFO: Normal.
PINCTRL DRIVER|INFO: mux reg: 0x40 = 0, input reg: 0x0 = 0, pad conf reg: 0x2a8 = 25. PINCTRL DRIVER|INFO: Normal.
PINCTRL DRIVER|INFO: mux reg: 0x60 = 6, input reg: 0x0 = 0, pad conf reg: 0x2c8 = 89. PINCTRL DRIVER|INFO: Normal.
PINCTRL DRIVER|INFO: mux reg: 0x48 = 0, input reg: 0x0 = 0, pad conf reg: 0x2b0 = 22. PINCTRL DRIVER|INFO: Normal.
PINCTRL DRIVER|INFO: mux reg: 0x4c = 0, input reg: 0x0 = 0, pad conf reg: 0x2b4 = 25. PINCTRL DRIVER|INFO: Normal.
PINCTRL DRIVER|INFO: mux reg: 0x68 = 0, input reg: 0x0 = 0, pad conf reg: 0x2d0 = 3. PINCTRL DRIVER|INFO: Normal.
...
PINCTRL DRIVER|INFO: pinctrl device initialisation done
MON|INFO: PD 'pinctrl' is now passive!
```

Then, the example client will run some tests on the driver to ensure it's arguments validation is correct:
```
client begin testing pinmux driver args validation:
PINCTRL DRIVER|ERROR: offset is out of bound
NULL offset...PASS
PINCTRL DRIVER|ERROR: offset is out of bound
PINCTRL DRIVER|ERROR: offset is out of bound
mux underflow offset...PASS
PINCTRL DRIVER|ERROR: offset is out of bound
mux overflow offset...PASS
PINCTRL DRIVER|ERROR: offset is not 4 bytes aligned
PINCTRL DRIVER|ERROR: offset is not 4 bytes aligned
unaligned offset...PASS
PINCTRL DRIVER|ERROR: offset is out of bound
gpr underflow offset...PASS
PINCTRL DRIVER|ERROR: offset is out of bound
gpr overflow offset...PASS
mux write first register...PASS
mux write last register...PASS
gpr write first register...PASS
gpr write last register...PASS
all pinmux driver arguments validation tests passed...continuing
```

Once all checks and initialisation are complete, the client will print an incrementing integer every second. If the second is an even number, the UART1_TX pad will be connected to the UART1_TX pin. If the second is an odd number, the UART1_TX pad will be connect to the ECSPI3_MOSI pad, so you won't see odd seconds being printed:
```
client hello #0
client hello #2
client hello #4
client hello #6
client hello #8
client hello #10
...
```