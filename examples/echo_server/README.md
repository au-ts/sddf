<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Network echo server

This example shows off the networking sub-system by having
[lwIP](https://savannah.nongnu.org/projects/lwip/) based clients talking to an ethernet device.

Each client simply accepts RX traffic and sends it back out (hence the name 'echo server').

The system is setup with two of these 'echo server' clients that share the same ethernet
device.

## Architecture

![echo server architecture](./docs/echo_server.svg)

You can see from above that a number of components are involved.

This echo server system is what we use to test our ethernet drivers as well as benchmark
their performance.

In addition to an ethernet driver, we also make use of a serial driver and timer driver.
The serial driver is used for logging DHCP messages, benchmarking results, etc.
The timer driver is used as the IP stack needs to be able to set regular timeouts to function.

To learn more about the benchmarking architecutre and setup, see the
[benchmarking section below](#benchmarking).

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

### Testing

If you would like to test that the system is reachable, you can run the command
below which simply checks that both the UDP socket and TCP socket can echo
a single packet:
```sh
python3 scripts/connect.py [ip address]
```

You should see the following output:
```
SUCCESS: Received UDP response
SUCCESS: Received TCP response
```

## Benchmarking

To benchmark the system we make use of the [ipbench project](https://github.com/au-ts/ipbench)
to apply load to the system and record results such as throughput, latency, and CPU utilisation
figures.

For benchmarking, we have two specific PDs as part of the system:

* the benchmark PD
* the bench idle PD

The benchmark PD is responsbile for using the PMU hardware to record performance events such as
cycle counts and manage the start/stopping of benchmark runs.

Typically our setup is that ipbench will begin a benchmarking run for each throughput we want
to measure. For example, we typically measure the performance of the echo server for throughput
load at 10Mb/s, 20Mb/s, 50Mb/s, 100Mb/s, 200Mb/s, 300Mb/s and so on until 1000Mb/s since that
is typically the limit of the hardware.

The bench idle PD is responsible for recording the amount of cycles that were consumed
while the system was idle (as in, no other user-space or kernel threads were running).
This is so that we can get the CPU utilisation of the system.

### Running the benchmarks

> [!NOTE]
> Benchmarking is only supported for AArch64 boards, RISC-V benchmarking is not supported yet,
> see https://github.com/au-ts/sddf/issues/421 for details.

The benchmarks must be run with the Microkit `benchmark` configuration, e.g with
`MICROKIT_CONFIG=benchmark` as part of the `make` command.

Assuming you have ipbench setup, you can use the following script to run the benchmark:
```sh
python3 scripts/benchmark.py [target machine ip] --clients [ip addr(s) of ipbenchd systems]
```

Note that `--clients` here are the *load generators*, not the clients running in the
echo server system.

You can see all the possible arguments with
```sh
python3 script/benchmark.py -h
```

Note that for gathering benchmark results you should not change the default parameters
unless you have networking experience and understand the echo server system well.

## Debugging

If you are not seeing the DHCP messages from the clients or failing to run the benchmarks,
the below tips are useful for debugging.

Before actually trying to debug the echo server, it's important to ensure that the other
drivers in the system other than the networking driver work. You can do this by looking
at the [timer](../timer/README.md) and [serial](../serial/README.md) examples. The client
IP stack relies on a functioning timer driver, without it even DHCP will fail.

Once you are confident that the other drivers are working, you can begin debugging the
echo server.

Other than adding debug prints in the ethernet driver to check that IRQs are occuring
(to ensure RX/TX traffic is happening), the main helper is to increase the amount of
logging in lwIP.

The header `include/lwip/lwipopts.h` describes a number of lwIP configuration options.
`LWIP_DBG_MIN_LEVEL` can be changed to `LWIP_DBG_LEVEL_ALL`. You can also enable prints
in other components of LWIP, (e.g. `#define DHCP_DEBUG LWIP_DBG_ON`).
