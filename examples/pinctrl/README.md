<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Pinctrl example

This is an example to show a system using multiple physical peripherals with the pinctrl driver.

## Building

The following platforms are supported:
* imx8mm_evk
* imx8mp_evk
* imx8mq_evk
* maaxboard

### Make

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board> MICROKIT_CONFIG=<debug/release/benchmark>
```

After building, the system image to load will be `build/loader.img`.


## Running

@billn update

<!-- When running the example you should the following output:
```sh
Begin input
'client0' is client 0
'client1' is client 1
Hello world! I am client1.
Please give me character!
Hello world! I am client0.
Please give me character!
```

Some of the output will be in red (client 0), some of it will be in green (client 1).
When typing in characters into your terminal, you should see them be printed in the
output, by default these will be red for client 0.

To switch clients, enter:
```sh
CTRL + \ + <client number>
```

For example, to switch to client 1, enter:
```sh
CTRL + \ + 1
```

You should see the following output when doing so:
```
VIRT_RX|LOG: switching to client 1
``` -->

## Configuration

@billn fill in

## Example

@billn fill in
