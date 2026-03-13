<!--
    Copyright 2025, UNSW
    SPDX-License-Identifier: CC-BY-SA-4.0
-->

# i.MX8 Platform-specific pinctrl details

Prerequisite reading:
1. [pinctrl.md](../pinctrl.md)

Each device's state will appear as a pin configuration node in the pinctrl device. A pin
configuration node will contain all the data necessary for the pin controller configure all required
pins to the correct state. Each pin's configuration data is encoded as an entry of 6 32-bit
integers in the `fsl,pins` prop of the pin configuration node.

An entry is of the form < mux_reg conf_reg input_reg mux_val input_val pad_setting >. Where:
- "mux_reg" indicates the offset of mux register.
- "conf_reg" indicates the offset of pad configuration register.
- "input_reg" indicates the offset of select input register.
- "mux_val" indicates the mux value to be applied.
- "input_val" indicates the select input value to be applied.
- "pad_setting" indicates the pad configuration value to be applied.

For example (from `maaxboard.dts`):
```
uart2grp {
    fsl,pins = <0x23c 0x4a4 0x4fc 0x00 0x00 0x49 0x240 0x4a8 0x00 0x00 0x00 0x49>;
    phandle = <0x25>;
};
```

So `uart2` requires two pins. The first pin need:
mux_reg   @ 0x23c = 0x0
conf_reg  @ 0x4a4 = 0x49
input_reg @ 0x4fc = 0x0

To decode what these numbers mean, we start by consulting the datasheet (i.MX 8M Dual/8M QuadLite/8M
Quad Applications Processors Reference Manual IMX8MDQLQRM Rev 3.1, 06/2021). At page 1581, section
8.2.5.139 we know that the register `mux_reg @ 0x23c` is called `IOMUXC_SW_MUX_CTL_PAD_UART2_RXD`.
Which controls what signal line inside the chip the `UART2_RXD` pad on the chip package will be
connected to. By setting this register to zero, we connect this pad to the RX line of UART2.

Then, `conf_reg @ 0x4a4` is the `IOMUXC_SW_PAD_CTL_PAD_UART2_RXD` register that controls the
electrical characteristic of the `UART2_RXD` pad. We convert `0x49` to binary `0b1001001`. By
superimposing the binary value onto the register map in section 8.2.5.293 on page 1813. We can
decode that by setting `conf_reg` to 0x49, we achieve:
- Drive strength: 255_OHM — 255 Ohm @3.3V, 240 Ohm @2.5V, 230 Ohm @1.8V, 265 Ohm @1.2V,
- Medium Frequency Slew Rate (100Mhz),
- Open Drain Disabled,
- Pull Up Resistor Disabled, and
- Schmitt Trigger Enabled for this pad.

While it is not necessary for you to understand what all of this registers mean, it is still useful
to be aware of how they roughly function for debugging purposes.