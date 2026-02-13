<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Network echo server

This example demonstrates how the [networking
subsystem](/docs/network/network.md) can be used to construct a simple and
performant 'echo server', which echoes back UDP and TCP traffic received on
pre-configured ports. As is typical in [LionsOS](https://lionsos.org) systems,
each client contains its own user-space
[lwIP](https://savannah.nongnu.org/projects/lwip/) IP stack which interfaces
with the sDDF networking queues using our sDDF lwIP glue library
[libsDDFlwIP](/docs/network/network.md#lib-sddf-lwip). The use of libsDDFlwIP
also ensures that each client implements the [signalling
protocol](/docs/network/network.md#network-signalling-protocol) correctly.

As well as echoing received traffic, clients also run an
[ipbench](https://github.com/au-ts/ipbench) benchmarking daemon allowing them to
participate in throughput, utilisation and latency testing while echoing back
variable loads of UDP and TCP traffic. More on this can be found in the
[benchmarking](#benchmarking) section.

By default the example system contains two 'echo server' components, both of
which are clients of the networking subsystem which shares a single ethernet
device. This echo server system is what we use to test our ethernet drivers and
benchmark their performance.

## System architecture

The following diagram shows the system architecture of the echo server example
system: ![echo server architecture](./docs/echo_server.svg)

The arrows of the diagram point in the direction of active data flow, but in the
case of the networking subsystem free buffers are returned in the opposite
direction.

The echo server system utilises the serial and timer subsystems in addition to
the networking subsystem. The serial subsystem is used by the echo server
clients for logging DHCP messages, and by the benchmarking component to print
results. The timer subsystem is used by the echo server clients to create the
regular timeouts that the IP stack requires to function.

In addition to an ethernet driver, we also make use of a serial driver and timer driver.
The serial driver is used for logging DHCP messages, benchmarking results, etc.
The timer driver is used as the IP stack needs to be able to set regular timeouts to function.

To learn more about the benchmarking architecture and setup, see the
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
* rock3b
* star64
* x86_64_generic (only QEMU right now)

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

This indicates that each client has successfully completed DHCP and printed its
IP address. Clients will subsequently listen on the following ports for the
listed traffic types:

| Port | Protocol | Behaviour |
|------|----------|-----------|
| 1235 | UDP | Echo back to sender |
| 1236 | TCP | Echo back to sender |
| 1237 | TCP: ipbench daemon | Benchmarking co-ordination and utilisation reporting |

Note that these port numbers are configured
[here](/examples/echo_server/include/echo.h).

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

The QEMU command invoked by the echo server makefile assumes the use of QEMU's
default address ranges, thus will need to be updated accordingly if you wish to
customise these.

The command enables both echo server clients to be reachable by the host on all
ports they are listening on through the following guest to host port mappings:

| Guest client | Guest IP | Guest Port | Host port |
| ------------ | -------- | ---------- | --------- |
| client0 | (typically) 10.0.2.16 | 1235 | 1235 |
| client0 | (typically) 10.0.2.16 | 1236 | 1236 |
| client0 | (typically) 10.0.2.16 | 1237 | 1237 |
| client1 | (typically) 10.0.2.15 | 1235 | 1238 |
| client1 | (typically) 10.0.2.15 | 1236 | 1239 |
| client1 | (typically) 10.0.2.15 | 1237 | 1240 |

The guest is reachable by the host at `localhost`/0.0.0.0. Traffic received on
the mapped ports will be forwarded to QEMU, which will forward it the
corresponding guest client and set the source IP address to the QEMU network's
gateway IP address which is by default 10.0.2.2.

### Testing

If you would like to test that the system is reachable and echoing correctly,
you can run the Python `connect` script provided in the
[scripts](/examples/echo_server/scripts/) directory.  The script checks that
both the UDP socket and TCP socket can echo a single packet:

```sh
python3 scripts/connect.py [ip address] --udp_port [udp port] --tcp_port [tcp port]
```

The script optionally supports specifying a port number for UDP and TCP echo
traffic, which is required if the default numbers have been changed or you are
running the system virtually on [QEMU](#qemu). When running on QEMU, the
`ip_address` parameter should be set to 0.0.0.0.

Upon success you should see the following output:
```
SUCCESS: Received UDP response
SUCCESS: Received TCP response
```

If the system is non-responsive, the script will hang in a blocked state
awaiting a response.

Additionally, both echo server clients are also reachable and responsive to
`ping`s.

## Benchmarking

To benchmark the system we make use of the [ipbench
project](https://github.com/au-ts/ipbench) which coordinates a set of load
generators that send traffic to a *target*, and calculates performance metrics
based on the return traffic received. The ipbench benchmarking suite is
comprised of three types of actors:
- The ipbench *controller* which coordinates the benchmark and ultimately
  reports the results obtained by the clients and target.
- The ipbench *clients* which are the load generators that receive instructions
  from the controller and send and receive traffic to and from the target. In
  our benchmarks the clients run the
  [latency](https://github.com/au-ts/ipbench/tree/main/ipbench2/doc) test.
- The *target* system which is being measured. The target echoes back traffic
  received from the clients, and in the
  [cpu_target_lukem](https://github.com/au-ts/ipbench/tree/main/ipbench2/doc)
  test that we use it also coordinates with the controller to measure the
  utilisation of the system.

The client latency and target utilisation tests we use allow us to calculate:
- The proportion of traffic sent by the clients that is successfully echoed back
  by the target (i.e. achieved throughput in bits/s).
- The time taken for each response to be received (i.e. latency as minimum,
  median, mean and maximum round trip times).
- The CPU utilisation of the target system during each benchmark (i.e. the total
  number of CPU cycles that pass during the benchmark, as well as how many of
  those cycles were spent *idle* or not running user-space or kernel threads - a
  more precise explanation of this can be found in the [following
  section](#cpu-utilisation-and-pmu-data)).

For a full set of benchmarking results, we measure the performance of the system
using both UDP and TCP traffic, over a fixed set of incrementally increasing
throughput loads. The throughputs start small (10Mb/s, 20Mb/s, 50Mb/s, 100Mb/s)
and increase in increments of 100Mb/s until the maximum throughput of the NIC is
reached (normally 970Mb/s, which corresponds to an actual load of 1000mb/s when
accounting for the overhead of ethernet headers).

For a selected throughput, a benchmark run involves three phases, throughout all
of which traffic is sent by the clients to the target at the selected
throughput:
1. A warm-up phase for a fixed number of seconds.
2. The client latency testing phase where the clients begin taking statistics on
   packets received (RTT for responses and dropped packet counts). This phase
   will continue until the configured number of sample packets have been
   received by the clients, thus can vary in time significantly depending on the
   achieved throughput of the target. Note that if the target becomes
   unresponsive during this phase, or there is a large amount of packet loss
   ipbench will hang here.
3. A cool-down phase for a fixed number of seconds.

The latency and throughput measurements taken by the clients are based only on
the sampling phase, while the target CPU measurement is measured throughout all
three phases.

After the benchmark run is complete, the controller will write the results of
the test to both `stdout` and a configured file in the form of a `csv`.
Additionally, the benchmark PD in the echo server will print the [kernel tracked
utilisation and PMU data](#cpu-utilisation-and-pmu-data) over serial.

The default settings we use for these benchmarks can be found in the
`benchmark.py` script in the [scripts](/examples/echo_server/scripts/)
directory.

### CPU Utilisation and PMU data

Although the echo server client sends utilisation data to the ipbench
controller, the results themselves are largely independent from ipbench, and
only rely on the controller for start and stop times. The echo server system has
three mechanisms for measuring its performance which can be used simultaneously:
1. Kernel tracked utilisation OR kernel entries. Utilisation being total cycles,
   kernel cycles, kernel entries and number of schedules for each core and each
   PD. A choice between utilisation or kernel entries must be made as each
   requires a different benchmarking mode of the kernel.
2. Per-core system utilisation based on cycle counts measured by an idle thread.
3. PMU data, see below from the [benchmark PD](/benchmark/benchmark.c):

```c
char *counter_names[] = {
    "L1 i-cache misses",
    "L1 d-cache misses",
    "L1 i-tlb misses",
    "L1 d-tlb misses",
    "Instructions",
    "Branch mispredictions",
};
```

PMU and kernel tracked statistics are managed by the [benchmark
PD](/benchmark/benchmark.c), while total and idle cycle counts are maintained by
the [idle thread](/benchmark/idle.c). The idle thread has only one function
which is to maintain a count of total and idle core cycles which resides in
shared memory with the [benchmarking echo server
client](#difference-between-echo-server-clients). On system initialisation, the
idle thread enters an infinite loop of the following:
 * Read the current cycle count.
 * Calculate the difference from its last read.
 * If the difference is small enough (indicating it has not been pre-empted),
   those cycles are categorised as *idle* and added to the idle count.
 * Update the total cycle count.

Thus the idle thread maintains a page of shared memory that is used to calculate
system utilisation.

#### Benchmarking timeline

When an ipbench test begins, the following events occur inside the echo server
system:

START:
- Echo server client receives an ipbench `START` packet.
- Client takes a copy of the current total and idle cycle counts.
- Client notifies the benchmark PD.

BENCHMARK START:
- Benchmark PD resets PMU counters.
- Benchmark PD resets kernel utilisation OR kernel entries state.

STOP:
- Echo server client receives an ipbench `STOP` packet.
- Client takes a new copy of the current total and idle cycle counts.
- Client calculates the total and idle cycles expended during the benchmark.
- Client sends the calculated counts to the ipbench controller.
- Client notifies the benchmark PD.

BENCHMARK STOP:
- Benchmark PD reads and prints PMU counters to serial.
- Benchmark PD reads and prints kernel utilisation OR kernel entries to serial.

Unlike the ipbench controller data which is output as a csv, data printed by the
benchmark PD does not adhere to a standardised format. Thus, we have provided a
Python formatting script which can convert the echo server system output log
file into a series of result csvs. The script can handle the log file of a
system that has performed an arbitrary number of benchmarks by optionally
specifying a comma separated list of throughputs for each test:

```sh
python3 scripts/process_output.py [system output log file] [comma separated throughput]
```

> [!NOTE]
> There is a distinct difference between the system utilisation reported by the
> kernel and that reported by the echo server client using the idle thread. The
> approach of the idle thread to count idle cycles is inherently less accurate
> than that of the kernel, and has a tendency to attribute less cycles to the
> idle thread than the kernel (for example, the idle thread will not count
> kernel cycles involved in handling its own scheduling). You should expect CPU
> utilisation figures to be higher when obtained using the idle thread, e.g. a
> system utilisation of 65% tracked by the kernel may be up to 70% as tracked by
> the idle thread.

#### Difference between echo server clients

The two echo server clients are obtained from the same [c
file](/examples/echo_server/echo.c), however they have different Microkit system
information patched in during the build process. The main difference between
clients is that one is capable of orchestrating the benchmark process described
in the [timeline](#benchmarking-timeline), while the other is not. Both clients
run the ipbench daemon on the [utilisation
port](/examples/echo_server/utilization_socket.c), thus both will be capable of
participating in the protocol with the ipbench controller. However only one of
the clients has the idle thread cycle count page mapped into its address space,
as well as start and stop channels to the benchmark PD.

We refer to the client with the cycle counts and benchmarking channels as the
*benchmarking client*. This is by default client0. The other client, client1,
will simply report total and idle cycle counts of 0 to the ipbench controller if
it is the target of a benchmark.

> [!NOTE]
> If you wish to obtain total and idle cycles from ipbench, or kernel and PMU
> data from the echo server ensure that the target IP address is set to the IP
> address of client0. client1 will always report cycle counts of 0, and does not
> have the capability to communicate with the benchmarking PD.

### Running the benchmarks

> [!NOTE]
> Collecting PMU data while benchmarking is only supported for AArch64 boards,
> RISC-V benchmarking is not supported yet, see
> https://github.com/au-ts/sddf/issues/421 for details.

Although the echo server clients run the ipbench daemon on the utilisation port
in all Microkit configurations, utilisation and PMU data can only be obtained if
the system is built in the Microkit `benchmark` configuration, e.g with
`MICROKIT_CONFIG=benchmark` as part of the `make` command. Non-benchmark
configurations will report utilisation numbers as 0, and no PMU data will be
printed.

Assuming you have ipbench setup, you can use the following script to run the
benchmark. Note that the machine which runs this script will become the ipbench
[controller](#benchmarking) of all the benchmarks, and the script assumes that
the ipbench daemon of the clients are already running.
```sh
python3 scripts/benchmark.py [target machine ip] --clients [ip addr(s) of ipbenchd systems]
```

Ensure that the chosen target machine IP address is `client0`'s IP address [if
you wish to obtain valid utilisation numbers and PMU
data](#difference-between-echo-server-clients).

You can see all the possible arguments with
```sh
python3 scripts/benchmark.py -h
```

Note that for gathering benchmark results you should not change the default
parameters unless you have networking experience and understand the echo server
system well.

## Multicore

The echo server system can also run in a multicore configuration using the SMP
kernel. To build an SMP echo server system, pass the `SMP_CONFIG` variable as a
make argument when building the system:

```sh
make MICROKIT_BOARD=<board> MICROKIT_SDK=<path/to/sdk> MICROKIT_CONFIG=(benchmark/release/debug) SMP_CONFIG[= core configuration file]
```

If `SMP_CONFIG` is passed alone, the system will default to the following
configuration on 4 cores:

```json
{
    "timer_driver": 0,
    "serial_driver": 0,
    "serial_virt_tx": 0,
    "ethernet_driver": 1,
    "net_virt_tx": 1,
    "net_virt_rx": 0,
    "client0": 2,
    "client0_net_copier": 2,
    "client1": 3,
    "client1_net_copier": 3
}
```

Otherwise, this variable can be set to the path of a core configuration file of your
choosing following the format of the example files provided
[here](/examples/echo_server/core_config). You must ensure that all PDs in the
system are allocated to a core, or the system will fail to build.

To benchmark a multicore echo server system, the benchmark and idle PDs
[described above](#cpu-utilisation-and-pmu-data) will need to be duplicated so
that each core that contains active echo server PDS has its own benchmark and
idle PD. This is because cycle counts and PMU data are obtained on a per-core
basis. The creation of these PDs will be handled automatically by the echo
server [metaprogram](/examples/echo_server/meta.py). When a core configuration
file is provided, the metaprogram will read the file and determine which cores
are in use, creating all the required system infrastructure.

During a multicore benchmark, the system transitions through the following
events:

START:
- Echo server client receives an ipbench `START` packet. Continues as per single
  core description.
- Echo server client notifies the benchmark PD on the first active core.

BENCHMARK 0 START (If core 0 is active):
- Benchmark PD on core 0 receives notification from client. Continues as per
  single core description.
- Benchmark PD on core 0 notifies the benchmark PD on next active core (if such
  a core exists).

BENCHMARK 1 START (If core 1 is active):
- Benchmark PD on core 1 receives notification from client or previous benchmark
  PD. Continues as per single core description.
- Benchmark PD on core 1 notifies the benchmark PD on next active core (if such
  a core exists).

BENCHMARK 2 START (If core 2 is active):
- Benchmark PD on core 2 receives notification from client or previous benchmark
  PD. Continues as per single core description.
- Benchmark PD on core 2 notifies the benchmark PD on next active core (if such
  a core exists).

BENCHMARK 3 START (If core 3 is active):
- Benchmark PD on core 3 receives notification from client or previous benchmark
  PD. Continues as per single core description.

The same chain of notification occurs when a stop packet is received by the
client. Upon completion of the benchmarks, each benchmark PD will print the
core's results in the order in which they are notified.

## Debugging

If you are not seeing the DHCP messages from the clients or you are failing to
run the benchmarks, you may find the tips below to be helpful.

Before actually trying to debug the echo server, it's important to ensure that
the other drivers in the system other than the networking driver work. You can
confirm this by building and running the [timer](../timer/README.md) and
[serial](../serial/README.md) example systems. The client IP stack relies on a
functioning timer driver to provide timeouts and schedule callbacks, so if these
ticks are failing the echo server clients will not engage in retries which
effects the reliability of the DHCP protocol.

Once you have established the supporting subsystems are functional, you can
begin debugging the echo server.

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
