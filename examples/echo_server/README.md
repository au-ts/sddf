<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Network echo server

This example shows off the networking sub-system by having a
[lwIP](https://savannah.nongnu.org/projects/lwip/) based clients talking to an ethernet device.

The client simply accepts RX traffic and sends it back out (hence the name 'echo server').

The system is setup with two of these 'echo server' clients that share the same ethernet
device.

## Building

The following platforms are supported:

* imx8mm_evk
* imx8mp_evk
* imx8mp_iotgate
* imx8mq_evk
* maaxboard
* odroidc2
* odroidc4
* qemu_virt_aarch64
* qemu_virt_riscv64
* star64

To compile the system image, run:

```sh
make MICROKIT_BOARD=<board> MICROKIT_SDK=<path/to/sdk> MICROKIT_CONFIG=(benchmark/release/debug)
```

The system image will be at `build/loader.img`.

## Running

After loading the image, you should see the following logs:
```
DHCP request finished, IP address for netif client0 is: 10.0.2.16
DHCP request finished, IP address for netif client1 is: 10.0.2.15
```

You can see that each client has completed DHCP and printed out their IP address.

Each client listens on a number of ports for certain traffic:

| Port | Traffic |
|------|---------|
| 1235 | UDP packets |
| 1236 | Utilisation information, used during benchmarking |
| 1237 | TCP packets |

### QEMU

If you are on QEMU, the addresses printed out by the clients are relative to
QEMU's *internal* network. The QEMU command is run with arguments to explicitly forward
traffic on the same ports to the host.

This means that accessing localhost/0.0.0.0 on the host machine will send
and receive traffic to the same port within the emulated system.

Note that due to how QEMU handles forwarding packets using hostfwd, packets will be
sent to the default interface which has an IP address of `10.0.2.15`. If you wish to
target the other client, the `hostfwd` rule will need to be changed to specifically
target that IP address.

## Benchmarking

In order to run the benchmarks, set `MICROKIT_CONFIG=benchmark`. The system has
been designed to interact with [ipbench](https://sourceforge.net/projects/ipbench/)
to take measurements.

> [!NOTE]
> Benchmarking is only supported for AArch64 boards, RISC-V benchmarking is not supported yet,
> see https://github.com/au-ts/sddf/issues/421 for details.

Checks to make before benchmarking:

* Turn off all debug prints.
* Run with LWIP asserts turned off as well (`LWIP_NOASSERT`).
* Make sure compiler optimisations are enabled.
