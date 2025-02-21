<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# GPIO example

This example makes use two circuits. There is no debouncer added so it may not be fully accurate.

### Circuit 1:

GPIO_H_5 --------|>|----[R]-------- GND
                LED(2V)

Add appropriate resistance.

### Circuit 2:

GPIO_X_17 ----[ ]---- VCC (3.3)
          Button

## Building

### Make

To build the image, run the following command:
```sh
make MICROKIT_SDK=/path/to/sdk
```

The final bootable image will be in `build/loader.img`.

## Running GPIO

Running the example will show the following output after the system has booted:

```
GPIO DRIVER|INFO: Driver Init!
GPIO DRIVER|INFO: Driver Notified 52!
CLIENT|INFO: Init
CLIENT|INFO: Client Main!
CLIENT|INFO: Setting direction of GPIO1 to output!
CLIENT|INFO: Checking with get request!
CLIENT|INFO: Setting GPIO1 to on!
CLIENT|INFO: Checking with get request!
CLIENT|INFO: Setting GPIO1 drive strength to 4000UA!
CLIENT|INFO: Checking with get request!
CLIENT|INFO: Setting GPIO1 to off!
CLIENT|INFO: Checking with get request!
CLIENT|INFO: Setting direction of GPIO2 to input!
GPIO DRIVER|INFO: Driver Notified 52!
CLIENT|INFO: Checking with get request!
CLIENT|INFO: Setting pull of GPIO2 to down!
CLIENT|INFO: Checking with get request!
CLIENT|INFO: Setting gpio2s irq channel to be rising edge!
CLIENT|INFO: Checking with get request!
CLIENT|INFO: Setting gpio2s irq channel to have a filter!
GPIO DRIVER|INFO: Driver Notified 52!
CLIENT|INFO: Checking with get request!
CLIENT|INFO: Button now ready to be pressed!
CLIENT|INFO: Waiting for IRQ from driver!
CLIENT|INFO: Received!
CLIENT|INFO: Turned on!
CLIENT|INFO: Waiting for IRQ from driver!
```

Press the button.
Light should turn off.

```
GPIO DRIVER|INFO: Driver Notified 52!
CLIENT|INFO: Received!
CLIENT|INFO: Turned off!
CLIENT|INFO: Waiting for IRQ from driver!
```

Press the button.
Light should turn on.

```
GPIO DRIVER|INFO: Driver Notified 52!
CLIENT|INFO: Received!
CLIENT|INFO: Turned on!
CLIENT|INFO: Waiting for IRQ from driver!
```

# where i got up to last time
make claen to show up all of the wanring
or just dont compile with errors
