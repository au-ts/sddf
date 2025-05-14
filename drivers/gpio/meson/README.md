<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# ODROID C4 GPIO Specifications

## GPIO Output, Input and Configuration

### GPIO Banks
There are 9 GPIO banks all with different numbers of pins:
- GPIO_Z : 0 - 15
- GPIO_A : 0 - 15
- BOOT   : 0 - 15
- GPIO_C : 0 - 7
- GPIO_X : 0 - 19
- GPIO_H : 0 - 8
- GPIO_E : 0 - 2
- TEST_N : 0 - 0
- GPIO_AO : 0 - 11

### Hardware Registers
Each bank has an associated register(s) to configure the respective functionality for any of its pins:
- PREG_PAD_O is used to control the output of the pad.
- PREG_PAD_I is used to store the input value of the pad.
- PREG_PAD_EN_N is used to enable GPIO output function.
- PAD_PULL_UP_EN is used to enable the pull-up function of GPIO pad.
- PAD_PULL_UP is used to control GPIO PAD to be whether pull-up or pull-down.
- PAD_DS is used to control drive strength {ds1, ds0}.

There is also a lock register to lock the pin values of any of the GPIO_AO pins - **unimplemented**.

## GPIO IRQ Control

### IRQ sources
There are 8 interupt sources that can be configured to ANY of the pins in ANY of the GPIO banks.

- 103 : gpio_irq[7]
- 102 : gpio_irq[6]
- 101 : gpio_irq[5]
- 100 : gpio_irq[4]
- 99  : gpio_irq[3]
- 98  : gpio_irq[2]
- 97  : gpio_irq[1]
- 96  : gpio_irq[0]

There are also 2 AO interupt sources that can be configured to ONLY pins in the GPIO_AO bank.

- 239 : ao_gpio_irq1
- 238 : ao_gpio_irq0

Note: In theory since the input for the GPIO interrupt module comes directly from the I/O part of the pin, the pin doesn't neccessarily have to be configured as a GPIO pin and could be a UART TX pin driving the interrput source. 

### Hardware Registers
For each of the 10 interrupt sources, there is an associated (part of) register to configure the respective functionality:
- GPIO_BOTH_EDGE is used to configure a both edge generated interrupt (both rising and falling).
- GPIO_POLARITY is used to invert the GPIO signal.
- GPIO_EDGE_SEL is used to set as an edge generated interrupt or level-triggered interupt. Which edge is determined by GPIO_POLARITY.
- GPIO_PIN_SEL is used to select which GPIO pin is mapped to this interrupt.
- FILTER_SEL is used to select a value for filtering for the interrupt.

There is also a field specific to the 2 AO interupt sources:
- GPIO_FILTER_USE_CLK is used to connect the input filter to the system clock. **unimplemented**

## SPECIAL NOTES
- Out of the brought out pins, you cant seem to configure the GPIOA pins to pull down :(

