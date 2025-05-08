<!--
    Copyright 2025, UNSW
    SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Pin control driver
Also known as a pinmux or pinctrl driver

# Terminology
- Port: refers to an input or output line of a logic instance in the chip (e.g. UART, DDR, HDMI,
  I2C,...). For example, an I2C instance has SDA and SCL ports. Not to be confused with pad.
- Pad: refers to the physical pin on the chip package (example, ball for BGA packaged chips).
- Client device: a peripheral device on the board that needs pinctrl configuration.

# Overview
<!-- This paragraph was paraphrased from two documents:
Linux pinctrl documentation: https://www.kernel.org/doc/Documentation/pinctrl.txt
i.MX 8 Chapter 8 Chip IO and Pinmux:
https://community.nxp.com/pwmxy87654/attachments/pwmxy87654/imx-processors/213251/1/IMX8MPRM-TableMuxing.pdf -->
A chip contains a limited number of pads as it is not feasable to have a one-to-one mapping between
all pads and ports. Hence, most of the pads have multiple signal options. I.e. a pad can be
connected to one of multiple ports at a given point in time as appropriate for the intended use
case. These signal-to-pin and pin-to-signal options are selected by the input-output multiplexer
called a pin controller or pinmux. The pin controller is also used to configure other electronic
characteristics of a pin, such as drive strength, bias, etc. All of these configurations can be
programmed in software by writing to the pin controller's registers.

Before the pinctrl driver is built, a Python script will read the target board's device tree source
file, extracting all the pinctrl settings and encoding them as binary values in an assembly file.
Then the driver is built and linked with the pinctrl data assembly file, creating a complete pinctrl
driver ELF image.

The pinctrl driver must be exclusively run at the highest priority to ensure that it is the first PD
initialised in the system. So that all pads can be connected to the desired pins before any other
device drivers attempt to initialise. At `init()` time, the driver will read the encoded pinctrl
data and write it into the pinctrl device registers.

This driver is needed in two cases:
1. When the peripheral device you are using on your board isn't used by the bootloader. Thus some
   bootloader implementations may not bother to program the pinctrl registers pertaining to those
   client devices.
2. Some device drivers need to be able to dynamically configure the pinctrl characteristics at
   run-time. For example, to switch the SD Card into a higher speed state on the i.MX8 and Meson
   platforms, the pinctrl registers must be reprogrammed to handle the higher speed. Though this is
   future work.

# Data Structure
This section describe how the pinctrl data is encoded in the DTS and how it get organised by the
Python script for the C driver. This information is universal to all platforms.

At the top level, we have an array of all the client devices that needs the pinmux. Each device may
have multiple pinctrl states to select from, and each state has an associated set of pin
configurations.

For example, with the SD Card reader on the MaaXBoard:
```
mmc@30b40000 {
    compatible = "fsl,imx8mq-usdhc\0fsl,imx7d-usdhc";
    reg = <0x30b40000 0x10000>;
    interrupts = <0x00 0x16 0x04>;
    clocks = <0x02 0xec 0x02 0x69 0x02 0xd2>;
    clock-names = "ipg\0ahb\0per";
    assigned-clocks = <0x02 0x8e>;
    assigned-clock-rates = <0x17d78400>;
    fsl,tuning-start-tap = <0x14>;
    fsl,tuning-step = <0x02>;
    bus-width = <0x04>;
    status = "okay";
    pinctrl-names = "default\0state_100mhz\0state_200mhz";
    pinctrl-0 = <0x3d>;
    pinctrl-1 = <0x3e>;
    pinctrl-2 = <0x3f>;
    non-removable;
    no-sdio;
    no-1-8-v;
};

iomuxc@30330000 {
    compatible = "fsl,imx8mq-iomuxc";
    reg = <0x30330000 0x10000>;
    pinctrl-names = "default";
    pinctrl-0 = <0x13>;
    phandle = <0x11>;

    imx8mq-evk {
        ...
        usdhc1grp {
            fsl,pins = <0xa0 0x308 0x00 0x00 0x00 0x83
            0xa4 0x30c 0x00 0x00 0x00 0xc3
            0xa8 0x310 0x00 0x00 0x00 0xc3
            0xac 0x314 0x00 0x00 0x00 0xc3
            0xb0 0x318 0x00 0x00 0x00 0xc3
            0xb4 0x31c 0x00 0x00 0x00 0xc3
            0x40 0x2a8 0x00 0x00 0x00 0x19>;
            phandle = <0x3d>;
        };

        usdhc1grp100mhz {
            fsl,pins = <0xa0 0x308 0x00 0x00 0x00 0x85
            0xa4 0x30c 0x00 0x00 0x00 0xc5
            0xa8 0x310 0x00 0x00 0x00 0xc5
            0xac 0x314 0x00 0x00 0x00 0xc5
            0xb0 0x318 0x00 0x00 0x00 0xc5
            0xb4 0x31c 0x00 0x00 0x00 0xc5
            0x40 0x2a8 0x00 0x00 0x00 0x19>;
            phandle = <0x3e>;
        };

        usdhc1grp200mhz {
            fsl,pins = <0xa0 0x308 0x00 0x00 0x00 0x87
            0xa4 0x30c 0x00 0x00 0x00 0xc7
            0xa8 0x310 0x00 0x00 0x00 0xc7
            0xac 0x314 0x00 0x00 0x00 0xc7
            0xb0 0x318 0x00 0x00 0x00 0xc7
            0xb4 0x31c 0x00 0x00 0x00 0xc7
            0x40 0x2a8 0x00 0x00 0x00 0x19>;
            phandle = <0x3f>;
        };
        ...
    }
}
```

The prop `pinctrl-names` tells us how many pinctrl states a client device supports and the names of
the states.

The order of the state names correspond to the `pinctrl-[0-9]+` prop. So the phandle in `pinctrl-0`
will lead us to the node in the pinctrl device that contains the correct register values that we
need to write for the `default` pinctrl configuration of that client device.

# Current Implementation
The pinctrl driver will always set the `default` configuration on boot up. Supporting dynamic
setting of pinctrl state at run-time is future work.

# Supported Platforms
Please see [drivers.md](../../docs/drivers.md).

# Platform specific details
Please see the README.md inside the respective platform's pinctrl folder.