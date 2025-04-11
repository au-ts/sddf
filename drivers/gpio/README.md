<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->


# sddf-gpio-driver

This repo contains a gpio (general purpose input and output) driver for the ODROID C4 Single Board Computer built over the seL4 Device Driver Framework. This class is structured to be as generic as possible for future extension to other devices.

When a digtial I/O pin is not being used for any specific purpose (i2c, uart) it is implicitly converted to a GPIO pin.

# USAGE!!!!!!!!!!! (IMPORTANT)
There must be a configuration file that contains gpio_channel_mappings.

Some registers have undefined permissions so it is the clients responsibility to check with a GET request after each SET request to make sure what they are trying to do actually is reflected in the register!

Or check the datasheet (its wrong though sometimes).

We could make the driver check on each set request as well and return an error if its writes arent showing up. **unimplemented**

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
