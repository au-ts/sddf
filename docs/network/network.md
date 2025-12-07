<!--
    Copyright 2025, UNSW
    SPDX-License-Identifier: BSD-2-Clause
-->

# sDDF network subsystem

## System architecture

The network subsystem adheres to the sDDF design principles of modular
components split via separation of concerns. The subsystem broadly performs two
functions - securely multiplexing the ethernet device between isolated clients,
and providing a platform independent abstraction layer over all the hardware.
These functions are split into separate Microkit Protection Domains (PDs), and
in the case of multiplexing this is split further into receive (Rx) and transmit
(Tx) components.

Since each PD has a restricted set of responsibilities, they can be implemented
with minimal complexity and only require capabilities to a restricted subset of
the surrounding system. An example of this being our ethernet drivers *do not*
have the Rx or Tx DMA regions mapped into their address space, since they only
require the IO addresses of these regions to enqueue them into the NIC's
hardware rings.

![Networking subsystem architecture](/docs/network/imgs/network_arch.png)

The network subsystem is comprised of the following components, as shown in the
diagram:
* The ethernet driver which handles all NIC device interrupts, and is the only
  PD with access to the NIC's registers and hardware rings.
* The Rx virtualiser which is responsible for multiplexing the packets received
  by the NIC, and returning free buffers to the driver.
* The Tx virtualiser which is responsible for passing packets which clients wish
  to transmit to the ethernet driver, and returning free buffers back to the
  correct client upon completion.
* The (Rx) copy components which are responsible for copying packets residing in
  the Rx DMA region into [client-specific Rx data regions](#data-regions). In
  contrast to the other network components, each client [has its own copy
  component](#copy-components-and-availability).

Typically a networking client has both Rx and Tx capabilities, but the system
supports Rx and Tx only clients. Rx clients interface only with their respective
copiers to receive packets (or in the rare case where they are *trusted*, the Rx
virtualiser). Tx clients interface only with the Tx virtualiser to transmit
packets.

Network components communicate using shared memory (holding queues and data) and
asynchronous notifications (Microkit channels). The diagram below gives an
overview of how the queue metadata region is used to reference and organise
buffers in the data regions. For a more in depth discussion of these design
principles and how the network subsystem incorporates them, see the [sDDF design
document](/docs/design).

![Queue metadata regions](/docs/network/imgs/metadata.svg)


### Data regions

There are two types of regions used to hold data in the networking subsystem -
regions that are used by the NIC to perform DMA into and out of (referred to as
DMA regions), and regions that hold data belonging to a particular client
(referred to as client data regions).

DMA regions are used *either* for Rx or Tx. In the case of Tx, each client is
allocated its own Tx DMA region which it has exclusive access to. The only other
component that has permissions to a client's Tx DMA region is the Tx
virtualiser, which it requires for performing cache cleaning operations.

In contrast, as our multiplexing is performed by the virtualiser, all clients
share a single Rx DMA region. Since giving clients direct access to this global
region [poses a significant security issue](#copy-components-and-availability),
it is recommended that clients use a *copy* component which allows them be
allocated an exclusive Rx data region. In this case, a client's data region will
not be used for DMA and it will only ever contain packets addressed to that
client. The Rx DMA region will then only be accessible by the trusted Rx
virtualiser and copy components.

It is possible to connect a client *without* a copy component, however please
note that copiers play an [important safety
role](#copy-components-and-availability) in the system outside of just privacy,
and do not incur as large of a performance penality as you may think.

All data regions are broken into buffers of a fixed size of 2048 bytes (the
minimum size required to hold the ethernet MTU with the power of two
constraint). Since data regions must always be mapped into two address spaces,
buffers are always referenced using *offsets into data regions* rather than
virtual addresses. Components can use this offset to calculate a virtual since
each queue only holds references to buffers from a single region.

The only exception to this rule is the pair of queues shared between the Tx
virtualiser and the driver, since these queues hold buffers from each client's
Tx DMA region. This does not pose a problem, as in this case the virtualisers
use IO addresses instead of offsets. This allows the driver to pass these
addresses directly to the hardware without having knowledge of the underlying
data regions. When buffers are returned to clients, the Tx virtualiser can
determine their owner by comparing their address to the bounds of each client's
DMA region.

### Network queues

To facilitate the transfer of data buffers, neighbouring components use pairs of
single-producer single-consumer FIFO queues. We call the memory regions
containing these queues *metadata* regions. Note that these queues only contain
references to data, and are never used to store data themselves.

Network queues always come in pairs - an *active* queue for transferring buffers
containing *valid* or *active* data, and a *free* queue for returning *free*
buffers for reuse. Currently, the subsystem assumes that the free and active
queues will always be shared between the same two components, that is, if a
buffer is passed to a component for transmission or reception, it will always be
returned by the same component.

Each queue is implemented as a circular ring buffer, with entries being stored
in an array, and head and tail indices represented using overflowing unsigned
integers. Allowing head and tail indices to overflow optimises queue operations
and distinguishes between the empty and full condition, however it also enforces
that the queue capacities must be a power of two. While both the consumer and
producer of a queue need to read both indices, only the producer needs to modify
the tail, and only the consumer needs to modify the head. This enable all queue
operations to be lock-free, only requiring memory barriers to enforce observable
ordering.

It is strongly recommended to use the network queue
[library](/include/sddf/network/queue.h) as it was carefully constructed to
implement the required memory barriers correctly. If you do interact with the
network queues directly, the library should be used as a guide.

While the `net_queue_t` data structure sits in shared memory, the
`net_queue_handle_t` wrapper data structure does not. The handle holds pointers
to the free and active queues as well as their *capacity* (both queues always
have [the same capacity](#queue-assumptions)). Capacity must be protected from
untrusted components as erroneous modifications can cause out-of-bounds queue
accesses, since queues must be accessed modulo this value. For this reason all
network queue library functions take `net_queue_handle_t` pointers as
parameters. Consequently all queue operations have "duplicate" APIs depending on
whether the target is the free or active queue.

The code snippet below shows the two APIs for checking whether a queue is full:

```c
/**
 * Check if the free queue is full.
 *
 * @param queue queue handle for the free queue to check.
 *
 * @return true indicates the queue is full, false otherwise.
 */
static inline bool net_queue_full_free(net_queue_handle_t *queue)
{
    return queue->free->tail - queue->free->head == queue->capacity;
}

/**
 * Check if the active queue is full.
 *
 * @param queue queue handle for the active queue to check.
 *
 * @return true indicates the queue is full, false otherwise.
 */
static inline bool net_queue_full_active(net_queue_handle_t *queue)
{
    return queue->active->tail - queue->active->head == queue->capacity;
}

```

Net queues also contain a `consumer_signalled` flag which is used by the
consumer for requesting a Microkit notification from the producer. For an in
depth discussion on how to use this flag correctly, see the section on the
[network signalling protocol](#network-signalling-protocol).

## Safety properties

The networking subsystem was designed to inherently satisfy certain security and
reliability properties. This section details these properties, as well as other
known vulnerabilities we are still working on.

### Memory barriers and atomicity

The network queue library is currently [undergoing
updates](https://github.com/au-ts/sddf/pull/523) to its use of memory barriers
to ensure that all operations are observably correct by both components. The
implementation is currently optimised so that less expensive barriers are used
when all components reside on the same core. Similar changes have recently been
made to the [serial subsystem](https://github.com/au-ts/sddf/pull/561).

### Data privacy

The design of the networking subsystem inherently keeps data transmitted by each
client private, since each client is allocated its own Tx data region shared
only with the transmit virtualiser.

Since we do not utilise any hardware multiplexing features, all packets are
DMA'd into one region. Although it is possible to give a client access to this
region, this should not be done unless the client is *trusted*. To protect the
privacy of clients (and the [availability](#copy-components-and-availability) of
buffers), each client is allocated its own Rx data region and *copy* component.
When the Rx virtualiser determines that a packet is addressed to a client, the
packet is transferred to to the client's copier component who copies the packet
from the Rx DMA region and into the client's Rx data region. This allows the Rx
DMA region to only be mapped into the Rx virtualiser and copy component's
address spaces. Client's Rx data regions are only shared with a client's copier.

The design ensures that both client Rx and Tx data regions are only shared with
trusted components of the networking subsystem, and no client has direct access
to the global Rx DMA region.

### Copy components and availability

While copy components were originally developed for protecting the privacy of
each client, they also ensure that Rx DMA buffers remain available to all
clients of the system. Giving untrusted clients direct access to DMA buffers
poses an issue if they are not promptly returned. In the networking subsystem,
we consider a buffer *owned* by a component once it has been enqueued in a queue
consumed by that component. Once a component owns a buffer, no other component
can reference or access that buffer.

On the Rx side, this clearly would pose a threat to system availability if
clients were able to take ownership of an arbitrary number of Rx DMA buffers.
Thus, when a copy component is used restricting client access to DMA buffers
both protects the data of all clients in the system, as well as ensuring that Rx
DMA buffers can be reused without dependence on client processing delays.
Copiers are written so that if a client is not keeping up with the load and they
are not producing free client buffers as quickly as new packets are being
received, incoming Rx DMA buffers will immediately be returned to the Rx
virtualiser without copying. This allows clients to process packets at any rate
they wish without causing packet loss for other clients in the system.

On the Tx side, since each client has its own DMA region it is up to them to
ensure that packets are transmitted (and therefore freed) on a timely basis.

### Invalid writes

Currently there are a few ways that untrusted clients can interfere with the
system by writing to shared memory regions:
1. Writing to the Rx DMA region has the potential to corrupt all packets
   received by the system. Thus, this region must be mapped in read-only with
   the exception of the Rx virtualiser which requires write access for cache
   operations.

2. While we rely on the assumption that the tail of queues are only modified by
   the producer, and the head of queues are only modified by the consumer, we
   currently have no protection against invalid writes. Invalid writes to either
   of these indices will cause queue corruption, potentially resulting in buffer
   loss or gain, or unpredictable queue processing behaviour.

   If an untrusted component experiences buffer loss, this loss will only be to
   that client's buffer pools. However in the case of buffer gain this does have
   the potential to [effect other clients in the system](#queue-assumptions). We
   hope to fix this issue in the near future by having trusted components keep
   copies of indices shared with untrusted neighbours allowing checks for
   invalid modifications to be performed.

3. While we consider buffers to be *owned* by the network subsystem once they
   have been enqueued in a system component's queue, there is currently nothing
   preventing a client from continuing to write to a buffer afterwards.

   On the Rx side, this would only serve to corrupt its incoming packets.
   However on the Tx side, this may pose a problem if we wish to provide a
   *packet filtering* layer, which would enable us to prevent clients
   masquerading as other clients (we hope to provide this functionality in the
   future). This could only be implemented effectively is we could prevent
   clients from modifying packets after they have been transmitted. To enable
   this, we plan on introducing a Tx copier in the future.

### Queue assumptions

Currently the network queues are designed to have the capacity to hold all
buffers simultaneously. Since queue entries themselves are only pointers to
buffers, this does not incur significant memory overhead. Thus, while processing
network queues components do not need to check whether a queue is *full* - they
only need to check whether queues are *empty*. Since checking for fullness
requires the use of memory barriers, this is a significant optimisation.

Unfortunately there is currently a vulnerability where untrusted clients are
able to insert *duplicate buffers* into their queues, which could cause a
trusted component to enqueue past the queue's capacity corrupting the queue. On
the Tx side this could unfortunately cause buffer loss of other clients since
the Tx virtualiser holds all client's buffers in a single queue. While
components interfacing with untrusted components *do* check that the client
provided buffer offsets are valid, they *do not* check for duplicate inserts of
system owned buffers. We plan on fixing this issue with buffer reference counts,
or with the use of a Tx copy component.

### Network signalling protocol

When a producer has enqueued buffers into a queue, or a consumer has dequeued
buffers from a queue, we say that *work* has been performed. In order for work
to continue, it is typical that the sharer of the queue will require a
notification in order to be scheduled.

In the network subsystem, only the producer of a queue notifies the consumer.
However, since all neighbouring components share a pair of queues with each
being the producer of one and the consumer of the other, it is always possible
for both components to notify each other.

To minimise unnecessary notifications, the networking subsystem uses the [sDDF
signalling protocol](/docs/developing.md#signalling-protocol), which utilises a
shared *notification flag* for the consumer to register for notifications from
the producer when work has been performed. Upon finishing enqueueing a batch of
buffers, the producer will check the *`consumer_signalled`* flag to determine
whether to notify the consumer.

The signalling protocol was designed to ensure that deadlocks can not occur as a
result of race conditions from setting and checking this flag. Failure to follow
this protocol correctly may result in data processing delays, or in the worst
case deadlocks.

If you wish to enable notifications using the `consumer_signalled` flag, setting
the flag alone is not enough to guarantee that the consumer will remain free
from deadlock. The signalling protocol also requires that the setter of the flag
"double-checks" the state of the queue before blocking. This protects against a
race condition that can occur in the rare case that the producer pre-empts the
consumer and processes the queue just before the consumer is able to set this
flag. Pseudo code demonstrating how to this "double-check" should be implemented
can be found [here](/docs/developing.md#signalling-protocol).

## Networking design

The networking subsystem provides an abstraction layer over the hardware that
allows clients to securely and efficiently share the NIC using an asynchronous
queue and buffer interface. Currently the subsystem *does not provide* an IP
stack, and instead clients receive entire ethernet packets within buffers.
Clients are required to run their own IP stack independent of the network
subsystem. For this, we typically utilise the light-weight IP stack
[lwIP](#lwip) which supports a buffer interface. We have also created a
[library](#lib-sddf-lwip) for interfacing between sDDF network queues and lwIP
since this typically requires similar operations regardless of function of the
end client.

One aspect of the networking design that is unusual is our choice of using MAC
addresses for identifying and multiplexing between clients. Since the design
currently requires each client to run its own IP stack, with the system
components having very little knowledge of the underlying network activity,
using different MAC addresses (and therefore different IP addresses) was the
simplest way for us to multiplex. This also requires us to run the NIC in
promiscuous mode, listening for all network traffic.

When traffic reaches the Rx virtualiser, the ethernet header is inspected to
determine whether the destination MAC address matches with one of the clients in
the system. If so, the packet is transferred to the copier of that client. If
the packet is instead a broadcast packet it will be forwarded to the copier of
all clients of the system.

In the future we are looking into the possibilities of verified network stacks,
as well as moving more layers of the IP stack into the trusted system, which
will allow us to multiplex on an IP port level.

### lwIP

While the sDDF network subsystem does not assume a particular IP stack, all of
our experimentation and development has been done with the
[lwIP](https://savannah.nongnu.org/projects/lwip/) stack.

#### Updating lwIP

The source for lwIP is currently vendored in the source for sDDF, to update lwIP
see this [script](/network/ipstacks/update_lwip.sh).

#### Lib sDDF lwIP

The sDDF lwIP library provides an interface layer between sDDF network queues
and the lwIP `pbuf` interface. The header for the library can be found
[here](/include/sddf/network/lib_sddf_lwip.h), and the code
[here](/network/lib_sddf_lwip/).

The library can be used with any lwIP configuration and API level, and only
requires a handful of functions to be called in the Microkit `init` and
`notified` functions. If you wish to use the library, follow these steps:
1. Include the [makefile snippet](/network/lib_sddf_lwip/lib_sddf_lwip.mk) in
   your system's makefile. The snippet allows you to create an archive for each
   library user to be linked with.

2. Users must initialise the library by calling the `sddf_lwip_init` function in
   their `init` function. Details on the parameters for this function can be
   found in the library's [header](/include/sddf/network/lib_sddf_lwip.h) file.

   This function also requires a config struct emitted by the [sdfgen](#sdfgen)
   tool.

   Once the library has been initialised, you must also make sure that lwIP's
   first IP stack timeout is set by calling `set_timeout(ch)`. This starts a
   chain of timeouts that must be continuously reset.

3. Include the following three functions in the user's `notified` function:
 * `sddf_lwip_process_rx()` in response to be notified by the Rx virtualiser.
   This passes incoming packets into the IP stack.
 * `sddf_lwip_process_timeout()` in response to receiving a timeout. This
   processes pending lwIP timeouts which is important for DHCP and TCP to work
   correctly.
 * After processing the timeout, you must ensure that the next timeout is set by
   calling `set_timeout(ch)`

The [echo server](/examples/echo_server/) provides an example for how the
library should be used. More details on using the library can be found in the
section [below](#using-the-network-subsystem).

## Performance

We regularly benchmark the networking subsystem using our [echo
server](/examples/echo_server/) example setup. This system simply echoes either
UDP or TCP traffic back to the sender while taking a set of utilisation and PMU
benchmarks co-ordinated by the echoing client. More documentation on this can be
found in the [example readme](/examples/echo_server/README.md). A disorganised
collection of years of benchmarking results can be found
[here](https://docs.google.com/spreadsheets/d/1d1hKhZVVbEvxm7ehs7sXc1KvGjfdJ0RHR4YiMPzR8O8/edit?gid=36748068#gid=36748068).

## Using the network subsystem

If you wish to use a platform that is not yet supported, you will need to create
your own ethernet driver to interface with the Rx and Tx network virtualisers.
See [here](/docs/developing.md) for tips on how to do this and
[drivers.md](/docs/drivers.md) for an existing list of all ethernet devices
supported.

### sdfgen

It is highly recommended to use the [Microkit sdfgen
tool](https://au-ts.github.io/microkit_sdf_gen/) to create sDDF and LionsOS
systems. System components are written with the assumption that the
[sdfgen](/docs/developing.md#the-metaprogram) tool will be used. This tool was
written to act as system glue, providing an abstract API for creating Microkit
system resources and emitting both the Microkit system description file as well
as binary data files for each component of the system. The data files provide
the system information needed for inter-component communication as well as other
functionalities like device information.

To add a *network system* in your Python metaprogram, you must first create
protection domains for each of the system components:
* The [ethernet driver](/drivers/network/) for your platform.
* The [receive](/network/components/virt_rx.c) and
[transmit](/network/components/virt_tx.c) network virtualisers.

Once these components have been declared, a sdfgen network subsystem can be
created:

```py
from sdfgen import SystemDescription, Sddf

ProtectionDomain = SystemDescription.ProtectionDomain

ethernet_driver = ProtectionDomain(
    "ethernet_driver",
    "eth_driver.elf",
    priority=101,
    budget=100,
    period=400,
    cpu=get_core("ethernet_driver"),
)

net_virt_tx = ProtectionDomain(
    "net_virt_tx",
    "network_virt_tx.elf",
    priority=100,
    budget=20000,
    cpu=get_core("net_virt_tx"),
)
net_virt_rx = ProtectionDomain(
    "net_virt_rx", "network_virt_rx.elf", priority=99, cpu=get_core("net_virt_rx")
)

net_system = Sddf.Net(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)

```

Once the system has been created, clients can be added along with their
respective [copy](/network/components/copy.c) components:

```py

client0 = ProtectionDomain(
    "client0", client0_elf, priority=97, budget=20000, cpu=get_core("client0")
)

client0_net_copier = ProtectionDomain(
    "client0_net_copier",
    client0_net_copier_elf,
    priority=98,
    budget=20000,
    cpu=get_core("client0_net_copier"),
)

net_system.add_client_with_copier(client0, client0_net_copier)
```

See the [sdfgen docs](https://au-ts.github.io/microkit_sdf_gen/) for more
details on the sdfgen network API like setting a client's MAC address, creating
a client with only Rx or Tx capabilities, or creating a trusted client without a
copier.

Note that priorities of network components are *configurable*, however the
system is designed with the assumption that the driver runs at the highest
priority, followed by the Tx virtualiser, the Rx virtualiser, and finally the
copiers and clients. sDDF generally prioritises the processing of Tx IRQs over
Rx IRQs to improve latency. If you wish to prioritise one client over another,
ensure this is reflected in the priority of their copiers as well. In the future
we will also be introducing the ability to customise the order in which clients
are processed by the Tx virtualiser, but currently clients are processed in the
order which they are added to the system.

If you wish for a client to use [lib sDDF lwIP](#lib-sddf-lwip), you will also
need to generate the resources needed for this in your metaprogram. This is
because the library requires dedicated lwIP memory pools proportional to the
number of client Rx buffers. To do this, add the following to your metaprogram:

```py
client0_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, client0)
```

Once all your system resources are created, ensure to connect and serialise the
data files each component needs to access them as follows:

```py
# serialise the network system data
assert net_system.connect()
assert net_system.serialise_config(output_dir)

# serialise the lib sDDF lwIP client data
assert client0_lib_sddf_lwip.connect()
assert client0_lib_sddf_lwip.serialise_config(output_dir)
```

This will create `.data` files in your selected build directory which you will
then need to `OBJCOPY` into the respective `.elf` files, see
[here](#building-components-and-libraries).

### Interfacing with clients

The Microkit sdfgen tool will create all the network resources required for each
network component. The virtual addresses of memory regions, channel values and
client information will be placed into serialised C structs and written to
`.data` files in the build director. These structs are called *config*
structures, and the *network* config structures are defined
[here](/include/sddf/network/config.h).

Each network client must declare a `net_client_config` struct for the system
data to be copied into. Clients must also declare network queue handles which
will be initialised with values from this config struct. Typically, a client's
network declarations will look as follows:

```c
#include <sddf/network/queue.h>
#include <sddf/network/config.h>

__attribute__((__section__(".net_client_config"))) net_client_config_t net_config;

net_queue_handle_t net_rx_handle;
net_queue_handle_t net_tx_handle;
```

These queues will need to initialised in the `init` function as follows:

```c
net_queue_init(&net_rx_handle, net_config.rx.free_queue.vaddr, net_config.rx.active_queue.vaddr,
                net_config.rx.num_buffers);
net_queue_init(&net_tx_handle, net_config.tx.free_queue.vaddr, net_config.tx.active_queue.vaddr,
                net_config.tx.num_buffers);
net_buffers_init(&net_tx_handle, 0);
```

Note that the `net_buffers_init` function fills the Tx free queue with all the
buffers belonging to the client. In the case of client Rx buffers, this is done
by the client's copy component.

If a client wishes to use [lib sDDF lwIP](#lib-sddf-lwip), a configuration
struct for this must also be declared, and the library must be initialised:

```c
#include <sddf/network/lib_sddf_lwip.h>
#include <sddf/timer/config.h>

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

__attribute__((__section__(".lib_sddf_lwip_config"))) lib_sddf_lwip_config_t lib_sddf_lwip_config;

sddf_lwip_init(&lib_sddf_lwip_config, &net_config, &timer_config, net_rx_handle, net_tx_handle, NULL, LWIP_TICK_MS, sddf_dprintf, netif_status_callback, NULL, NULL, NULL);
```

Note that the library also requires [timer](/docs/timer/timer.md) subsystem
access.


### Building components and libraries

Our build system relies on makefile snippets to build sDDF components and
libraries. The network components that need to be built are:
* The corresponding ethernet driver for your platform. The C code and makefile
  snippet for the driver can be found in the platform directory
  [here](/drivers/network/).
* The network virtualisers and copiers, whose makefile snippet can be found
  [here](network/components/network_components.mk).

These snippets will need to be included in your makefile.

Network components, along with most sDDF components rely on the sDDF debug
utility library (`libsddf_util_debug.a`) for debug prints and assertions. This
library will need to be a target of your makefile, and network components need
to be linked with it. The snippet for building the library can be found
[here](/util/util.mk).

If components in your system are using [lib sDDF lwIP](#lib-sddf-lwip), you will
also need to build an archive of the library for each component using this
[snippet](/network/lib_sddf_lwip/lib_sddf_lwip.mk).

Finally, you will need to ensure each `.elf` file has all the emitted `.data`
files from the metaprogram copied in. For network system components, this looks
as follows:

```sh
# device resources for the ethernet driver
$(OBJCOPY) --update-section .device_resources=ethernet_driver_device_resources.data eth_driver.elf
# network subsystem resources
$(OBJCOPY) --update-section .net_driver_config=net_driver.data eth_driver.elf
$(OBJCOPY) --update-section .net_virt_rx_config=net_virt_rx.data network_virt_rx.elf
$(OBJCOPY) --update-section .net_virt_tx_config=net_virt_tx.data network_virt_tx.elf
```

For network clients, there is one `.data` file for the network connection, and
one for lib sDDF lwIP if the library is in use. There is also a file for each
copy component:

```sh
$(OBJCOPY) --update-section .net_copy_config=net_copy_client0_net_copier.data network_copy.elf network_copy0.elf

$(OBJCOPY) --update-section .net_client_config=net_client_client0.data echo0.elf
$(OBJCOPY) --update-section .lib_sddf_lwip_config=lib_sddf_lwip_config_client0.data echo0.elf
```

#### Include paths

Network components and clients will need to have the top level [sDDF
include](/include/) in their `CFLAGS` to access sDDF library functions as well
as network configuration structs.

Components using lwIP will also require the lwIP include directories
`network/ipstacks/lwip/src/include`, `network/ipstacks/lwip/src/include/ipv4`.

## Running and using

An example echo server system utilising the network subsystem can be found
[here](/examples/echo_server/). The [README](/examples/echo_server/README.md)
describes how to build, run, test and benchmark the system.
