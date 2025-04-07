<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# IMX8MDQLQRM GPIO Specifications

## GPIO Output, Input and Configuration

### GPIO Instances
There are 5 GPIO instances each with varying amounts of ports(pins):
- GPIO_1 : 0 - 29
- GPIO_2 : 0 - 20
- GPIO_3 : 0 - 25
- GPIO_4 : 0 - 31
- GPIO_5 : 0 - 29

### Hardware Registers
Each instance has an associated register to configure the respective functionality for any of its pins:
- GPIO_DR is used to control the output of the pad, and read the input if direction is input.
- GPIO_GDIR is used to change the direction.
- GPIO_PSR is used to store the value of the corresponding input signal (if SION functionality is configured this will read the value of the pad even if mode is output or not GPIO).

The are for special gpio functionalities which are controlled via other registers associated with IOXMUXC. **unimplemented**

## GPIO IRQ Control

### IRQ sources

## IRQ sources
There are 8 single interupt sources that can be configured only to GPIO1's 8 low order interrupt sources (i.e. GPIO1 interrupt n, for n = 0 – 7).

- 56  : Active HIGH Interrupt from INT7 from GPIO
- 57  : Active HIGH Interrupt from INT6 from GPIO
- 58  : Active HIGH Interrupt from INT5 from GPIO
- 59  : Active HIGH Interrupt from INT4 from GPIO
- 60  : Active HIGH Interrupt from INT3 from GPIO
- 61  : Active HIGH Interrupt from INT2 from GPIO
- 62  : Active HIGH Interrupt from INT1 from GPIO
- 63  : Active HIGH Interrupt from INT0 from GPIO

There are also 10 combined interupt sources that can be configured to pins in the specified range for a specified instance.

- 64  : Combined interrupt indication for GPIO1 signal 0 throughout 15
- 65  : Combined interrupt indication for GPIO1 signal 16 throughout 31
- 66  : Combined interrupt indication for GPIO2 signal 0 throughout 15
- 67  : Combined interrupt indication for GPIO2 signal 16 throughout 31O
- 68  : Combined interrupt indication for GPIO3 signal 0 throughout 15
- 69  : Combined interrupt indication for GPIO3 signal 16 throughout 31
- 70  : Combined interrupt indication for GPIO4 signal 0 throughout 15O
- 71  : Combined interrupt indication for GPIO4 signal 16 throughout 31
- 72  : Combined interrupt indication for GPIO5 signal 0 throughout 15
- 73  : Combined interrupt indication for GPIO5 signal 16 throughout 31

### Hardware Registers
The 8 single interupt sources are active high and cannot be configured.

The 10 combined interrupt sources are configured directly through the pins that are on that line:
- GPIOx_ICR1 is used to configure interrupt configuration on the corresponding input signal.
- GPIOx_ICR2 is used to configure interrupt configuration on the corresponding input signal.
- GPIOx_IMR is used to mask(disable) the interupt on the corresponding input signal.
- GPIOx_EDGE_SEL is used to configure any edge on the corresponding input signal.

## SPECIAL NOTES


