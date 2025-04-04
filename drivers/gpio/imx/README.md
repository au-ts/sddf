<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->


# sddf-gpio-driver

Infomation in meson folder.

## IMX8MDQLQRM GPIO Specifications

### GPIO Output, Input and Configuration

#### GPIO Instances
There are 5 GPIO instances each with varying amounts of ports:
- GPIO_1 : 0 - 29
- GPIO_2 : 0 - 20
- GPIO_3 : 0 - 25
- GPIO_4 : 0 - 31
- GPIO_5 : 0 - 29

#### Hardware Registers
Each instance has associated register to configure the respective functionality for any of its pins:
- GPIO_DR is used to control the output of the pad, and read the input if direction is input.
- GPIO_GDIR is used to change the direction.
- GPIO_PSR is used to store the value of the corresponding input signal (if SION functionality is configured this will read the value of the pad even if mode is output or not GPIO).

The following are for special gpio functionality which are controlled via other registers associated with IOXMUXC.
TODO: add the IOXMUXC stuff

### GPIO IRQ Control

#### IRQ sources

#### Hardware Registers
