<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Serial example

This is an example to show multiple clients being used with a UART driver.

## Building

The following platforms are supported:
* odroidc2
* odroidc4
* imx8mm_evk
* imx8mp_evk
* imx8mq_evk
* maaxboard
* qemu_virt_aarch64
* qemu_virt_riscv64
* star64

### Make

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board> MICROKIT_CONFIG=<debug/release/benchmark>
```

After building, the system image to load will be `build/loader.img`.

If you wish to simulate on one of the QEMU platforms (qemu_virt_aarch64 or qemu_virt_riscv64),
you can append `qemu` to your make command to start QEMU after everything compiles.

### Zig

You can also build this example with the Zig build system:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=<board>
```

The options for `<board>` are the same as the Makefile.

You can simulate QEMU with:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=qemu_virt_aarch64 qemu
```

The final bootable image will be in `zig-out/bin/loader.img`.

## Running

When running the example you should the following output:
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
```

## Configuration
## Description
The serial server example system contains two clients which are both able to transmit and receive
characters over serial. The clients are based on the same executable generated from
`examples/serial/serial_server.c`.

The serial server client demonstrates two methods of outputting to serial: the first uses
`sddf_printf` (linked with `_sddf_putchar` defined in `util/putchar_serial.c`), and the second uses
`sddf_putchar_unbuffered` defined in the same file. 

The first method demonstrates character buffering based on a flush character or queue capacity, the
second demonstrates characters being transmitted in an unbuffered fashion, typically used by a REPL.

The serial server client sits in an event loop, awaiting notification from the receive virtualiser.
When a notification is received, the client outputs the character in an unbuffered fashion. Every 10
characters the client prints a message in a buffered fashion.

This notification handling process with the receive virtualiser demonstrates how the
*producer_signalled* flag is to be used to prevent against missed notifications from the virtualiser
which could result in missed characters or deadlock. 

In this example, **SERIAL_WITH_COLOUR** is enabled so each client prints with a
different colour.

char *serial_tx_data;
serial_queue_t *serial_tx_queue;
serial_queue_handle_t serial_tx_queue_handle;
```

If they require serial input then equivalent declarations must exist for the receive serial
objects. Finally, during initialisation and prior to calling printf, they must initialise their 
serial queue(s) by calling `serial_cli_queue_init_sys` as well as `serial_putchar_init` which
allows them to also use `sddf_putchar_unbuffered`.

## Example
The serial example system contains two clients which can both receive serial data as well
as transmit. By default, the example has SERIAL_WITH_COLOUR enabled so each client prints with a
different colour. Each client boots up and prints a hello world message when initialisation is
completed, and waits for input. When a character is received, each client will re-transmit the
character using `sddf_putchar_unbuffered` which flushes the character to the device immediately. Every
tenth character each client will print a string containing their name using `sddf_printf` which
calls the serial `_sddf_putchar`, flushing characters to the device only when a `\n` is
encountered.
## Documentation
Further documentation for the serial subsystem can be found in `docs/serial.md`
