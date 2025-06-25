<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# GPIO example

We have 2 GPIOs:
- `GPIO_1` is set to output.
- `GPIO_2` is set to input.

`GPIO_1` should be directly attached to `GPIO_2`.

Read `gpio_config.h` for details on which physical pins are being used.

## Building

The following platforms are supported:
* maaxboard

### Make

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board>
```

After building, the system image to load will be `build/loader.img`.

### Zig

You can also build this example with the Zig build system:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=<board>
```

The final bootable image will be in `zig-out/bin/loader.img`.

## Running

When running the example, you should see the following output:

```
CLIENT|INFO: Client Init!

CLIENT|INFO: Starting GPIO example! Note GPIO1 must be connected to GPIO2!

CLIENT|INFO: Setting direction of GPIO1 to output and intial value 0!
CLIENT|INFO: Setting direction of GPIO2 to input!
CLIENT|INFO: Checking (GPIO1's output == GPIO2's input)!
CLIENT|INFO: Setting value of GPIO1 to 1!
CLIENT|INFO: Checking (GPIO1's output == GPIO2's input)!
CLIENT|INFO: Now we will test IRQ functionality!
CLIENT|INFO: Setting type of IRQ of GPIO2 to falling edge!
CLIENT|INFO: Enabling IRQ functionality for GPIO2!
CLIENT|INFO: Setting a timeout for 1 second!
CLIENT|INFO: Setting value of GPIO1 to 0!
CLIENT|INFO: Main coroutine paused!
CLIENT|INFO: Got an interrupt from GPIO driver!
CLIENT|INFO: Got an interrupt from timer driver!
CLIENT|INFO: Main coroutine resumed!
CLIENT|INFO: Checking we recieved irq from GPIO2!
CLIENT|INFO: Setting type of IRQ of GPIO2 to rising edge!
CLIENT|INFO: Re-enabling IRQ functionality for GPIO2!
CLIENT|INFO: Setting a timeout for 1 second!
CLIENT|INFO: Setting value of GPIO1 to 1!
CLIENT|INFO: Main coroutine paused!
CLIENT|INFO: Got an interrupt from GPIO driver!
CLIENT|INFO: Got an interrupt from timer driver!
CLIENT|INFO: Main coroutine resumed!
CLIENT|INFO: Checking we recieved irq from GPIO2!
CLIENT|INFO: Re-enabling IRQ functionality for GPIO2!
CLIENT|INFO: Setting a timeout for 1 second!
CLIENT|INFO: Setting value of GPIO1 to 0!
CLIENT|INFO: Main coroutine paused!
CLIENT|INFO: Got an interrupt from timer driver!
CLIENT|INFO: Main coroutine resumed!
CLIENT|INFO: Checking we DIDN'T recieve irq from GPIO2!
CLIENT|INFO: Setting type of IRQ of GPIO2 to high level!
CLIENT|INFO: Setting a timeout for 1 second!
CLIENT|INFO: Checking we havent recieved any irq's from GPIO2!
CLIENT|INFO: Setting value of GPIO1 to 1!
CLIENT|INFO: Main coroutine paused!
CLIENT|INFO: Got an interrupt from GPIO driver!
CLIENT|INFO: Got an interrupt from timer driver!
CLIENT|INFO: Main coroutine resumed!
CLIENT|INFO: Checking we recieved irq from GPIO2!

CLIENT|INFO: IF YOU GOT THIS FAR EVERYTHING WENT SMOOTHLY!!!
```