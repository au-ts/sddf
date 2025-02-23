<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->


# sddf-gpio-driver

This repo contains a gpio (general purpose input and output) driver for the ODROID C4 Single Board Computer built over the seL4 Device Driver Framework. This repo is structured to be as generic as possible for future extension to other devices.

When a digtial I/O pin is not being used for any specific purpose (i2c, uart) it is implicitly converted to a GPIO pin.

# USAGE!!!!!!!!!!! (IMPORTANT)
There must be a configuration file that contains gpio_channel_mappings.

Some registers have undefined permissions so clients need to check with a get request after each set request to make sure what they are trying to do actually happens!!
Or check the datasheet.

Out of the brought out pins, GPIOA pins don't seem to work for input :(

## Design
- There is a single driver that controls all of both GPIO functionality and IRQ control.
- No virtualiser and instead everything is assigned in the system file and config file.

### Security
Security is currently enforced by the system designer.
There is no virtualiser to claim GPIO pins or IRQ channels.
Instead each channel from the client to the driver is assigned to either one GPIO pin and optionally an IRQ channel.
There is a gpio_config file where these details are specified.

### Clients
Clients PPC to the Driver in the channel associated with the GPIO or IRQ they want to configure.
More details later in PPC Communication Section.

### Driver
The driver is responsible for hardware interaction. It directly interacts with the gpio hardware.
It is also responsible for translating the requests from the client to perform the correct hardware interaction before returning if it was a success or failure.
It also forwards IRQs to the correct client as well.

### Transport
All requests (both SET and GET) transport is done through PPCs.
In the case where a client has subscribed to a certain IRQ,  when the device sends an IRQ to the driver, it is forwarded from driver to client.

### Communication

#### PPC
Note: The exact capabilities of GPIOs vary between systems.
Hence there is a common interface of labels, arguements, and formats that all GPIO drivers must understand.
Then there are platform specific interfaces in a seperate per-platform header.

Requests:

Label = either GET_GPIO, SET_GPIO, GET_IRQ or SET_IRQ.
Message Register 0 = The function we want to configure.
Message Register 1 = The value we want to set the function to (only used in SETs)

Responses
Label = either SUCCESS or FAILURE
Message Register 0 = either the Error that occured or the Value requested.

Then set the arguements of the PPC to specifically describe what you want to do
(outlined in include/sddf/gpio/gpio.h or include/sddf/gpio/{platform}/gpio.h depending on if its a common function or platform specific).

Where to actually place the arguements in the ppcs is the same for every platform gpio driver
(outlined in include/sddf/gpio/gpio.h).

#### IRQ
Irqs are recieved by driver and forwarded to associated client based on the config file.

## ODROID C4 GPIO Specifications

### GPIO Output, Input and Configuration

#### GPIO Banks
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

#### Hardware Registers
Each bank has an associated register(s) to configure the respective functionality for any of its pins:
- PREG_PAD_O is used to control the output of the pad.
- PREG_PAD_I is used to store the input value of the pad.
- PREG_PAD_EN_N is used to enable GPIO output function.
- PAD_PULL_UP_EN is used to enable the pull-up function of GPIO pad.
- PAD_PULL_UP is used to control GPIO PAD to be whether pull-up or pull-down.
- PAD_DS is used to control drive strength {ds1, ds0}.

There is also a lock register to lock the pin values of any of the GPIO_AO pins - **unimplemented**.

### GPIO IRQ Control

#### IRQ sources
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

#### Hardware Registers
For each of the 10 interrupt sources, there is an associated (part of) register to configure the respective functionality:
- GPIO_BOTH_EDGE is used to configure a both edge generated interrupt (both rising and falling).
- GPIO_POLARITY is used to invert the GPIO signal.
- GPIO_EDGE_SEL is used to set as an edge generated interrupt or level-triggered interupt. Which edge is determined by GPIO_POLARITY.
- GPIO_PIN_SEL is used to select which GPIO pin is mapped to this interrupt.
- FILTER_SEL is used to select a value for filtering for the interrupt.

There is also a field specific to the 2 AO interupt sources:
- GPIO_FILTER_USE_CLK is used to connect the input filter to the system clock. **unimplemented**
