<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Network iperf2 server

This example exploits the [LWIP iperf2 server](https://www.nongnu.org/lwip/2_1_x/group__iperf.html)
to create a benchmarking target for [iperf2](https://iperf.fr/iperf-doc.php#tuningtcp)
using the [networking subsystem](/docs/network/network.md).
Similarly to the iperf2 server example, we use our sDDF lwIP glue library
[libsDDFlwIP](/docs/network/network.md#lib-sddf-lwip).

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

After loading the image, you should see the following log:
```
DHCP request finished, IP address for netif client0 is: 10.0.2.16
```

This indicates that the client has successfully completed DHCP and printed its
IP address.

### QEMU

By default QEMU utilises a
[SLIRP](https://wiki.qemu.org/Documentation/Networking) networking backend,
which provides a virtual NAT'd network to your emulated system with a default
address range of 10.0.2.0/24. If you are running the system on QEMU, clients
will be allocated an IP address by QEMU's internal DHCP server starting from
10.0.2.15. Address allocation is based purely on the order in which clients
request an address, so there are no guarantees as to which address will be
allocated to which client (thus we have marked addresses as "typically" in the
table below).

The QEMU command invoked by the makefile assumes the use of QEMU's
default address ranges, thus will need to be updated accordingly if you wish to
customise these.

The guest is reachable by the host at `localhost`/0.0.0.0. Traffic received on
the mapped ports will be forwarded to QEMU, which will forward it the
corresponding guest client and set the source IP address to the QEMU network's
gateway IP address which is by default 10.0.2.2.

### Testing


## Benchmarking


## Debugging

If you are not seeing the DHCP messages from the clients or you are failing to
run the benchmarks, you may find the tips below to be helpful.

Before actually trying to debug the iperf2 server, it's important to ensure that
the other drivers in the system other than the networking driver work. You can
confirm this by building and running the [timer](../timer/README.md) and
[serial](../serial/README.md) example systems. The client IP stack relies on a
functioning timer driver to provide timeouts and schedule callbacks, so if these
ticks are failing the iperf2 server clients will not engage in retries which
effects the reliability of the DHCP protocol.

Once you have established the supporting subsystems are functional, you can
begin debugging the iperf2 server.

You can start by adding debug prints to the ethernet driver to confirm that IRQs
are occurring (to ensure RX/TX traffic is happening). Note that the ethernet
driver does not have access to serial printing, so for these prints to be
visible the system will need to be built in debug configuration
(`MICROKIT_CONFIG=debug`).

If you have found that the driver is receiving and transmitting traffic and
receiving IRQs, the next step is to look into the lwIP networking stack itself.
The IP stack supports a number of different debug logging configurations which
can be set by toggling the various `*_DBG` macros found in the [lwIP options
example header](/examples/echo_server/include/lwip/lwipopts.h). This header is
provided by the lwIP user and allows lwIP features to be turned on or off, thus
does not include a full list of available debug options. For this, you should
check the [options header in the lwIP
library](/network/ipstacks/lwip/src/include/lwip/opt.h). Any options you wish to
use can then be added the [lwIP options example
header](/examples/echo_server/include/lwip/lwipopts.h).

Each debug printing option you wish to use can be configured to the desired
level, see [here](/network/ipstacks/lwip/src/include/lwip/debug.h):

```c
/** Debug level: ALL messages*/
#define LWIP_DBG_LEVEL_ALL     0x00
/** Debug level: Warnings. bad checksums, dropped packets, ... */
#define LWIP_DBG_LEVEL_WARNING 0x01
/** Debug level: Serious. memory allocation failures, ... */
#define LWIP_DBG_LEVEL_SERIOUS 0x02
/** Debug level: Severe */
#define LWIP_DBG_LEVEL_SEVERE  0x03
```
