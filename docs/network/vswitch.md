<!--
    Copyright 2026, UNSW
    SPDX-License-Identifier: BSD-2-Clause
-->

# VSwitch component

The vswitch is an optional component of the sDDF networking stack. It models a
physical Ethernet switch with the ability to send and receive packets to all
network clients connected to it.

The vswitch supports a simple, static Access Control List (ACL) scheme in the
form of allow lists stating which clients can communicate with each other. The
communication can be uni or bi-directional.

With a vswitch one can create multiple isolated networks in a system,
maintaining the principle of confidentiality. Clients never receive buffers that
were not addressed to them, and if a client performs a broadcast transmission,
the ACL will filter out the destinations that the client is not permitted to
transmit to.

The vswitch also provides an API for clients to publish their IP addresses and
query the IP address of other reachable clients, allowing clients to discover
the IP addresses of their neighbours. More details on this vswitch PPC interface
can be found in the [Protected Procedure call](#protected-procedure-call-api)
section.

## System Architecture

Vswitch clients must be connected to the vswitch for both transmission and
reception. The transmit queues of vswitch clients are connected to the vswitch
component, as are the receive queues of the vswitch client's Copy component.
Thus all packets sent and received by vswitch client pass through the vswitch
component.

An example system with two vswitch clients and one non-vswitch client is shown
in the following figure:
![VSwitch in the system](/docs/network/imgs/vswitch.svg)

The abstraction the vswitch uses for a client (a pair of Rx and Tx queues) is a
*port*. See the following definition from the [network config
file](/include/sddf/network/config.h):

```c
typedef struct net_vswitch_port_config {
    net_connection_resource_t rx; // Rx queue of the port
    net_connection_resource_t tx; // Tx queue of the port
    region_resource_t tx_data; // Tx data region of the port
    mac_addr_t mac_addr; // MAC address of the port (ignored if virtualiser port)
    uint64_t acl; // Access control list of the port
} net_vswitch_port_config_t;
```

The final port in the vswitch's port list (port at index `config.num_ports`) is
the virtualiser port - the port which holds the connections with the Rx and Tx
virtualisers. In the virtualiser port, the Rx and Tx connections are reversed.
The Rx virtualiser is connected to the `tx` queue, and the Tx virtualiser is
connected to the `rx` queue. This allows the vswitch component to handle the
system receiving packets as the virtualiser port *transmitting* packets, and the
system transmitting packets as the virtualiser port *receiving* packets.

## Buffer Descriptor Region ID

The addition of a vswitch component requires that the system keep track of some
additional net buffer descriptor state in some circumstances. Namely the `oid`
or ownership identifier of a buffer.

Prior to the addition of the vswitch, the data region a buffer belonged to could
generally be inferred from the queue it was dequeued from. For example, a buffer
descriptor dequeued from a client's Tx active queue must refer to the client's
Tx data region. However, with the addition of the vswitch component, this can
not always be inferred.

For example, when the vswitch transmits a client's buffer to another client, the
copier of the destination client no longer knows which data region the buffer
belongs to. For queues where the buffer data region can no longer be inferred,
we now utilise the buffer descriptor `oid` field. The 6 bit integer held in this
field associates a region identifier with the buffer pointer to by the
descriptor.

If the data region of a buffer can still be inferred from the queue it was
dequeued from, the `oid` field should be set to 0 and safely ignored.

## Operation

### Unicast

The vswitch supports up to 31 ports (including the virtualiser port). When
packets arrive at a port (via the port's Tx queue), they are inspected against
an internal mapping of MAC addresses behind the other ports. If a port matching
the destination MAC address is not found, the packet is directed to the external
world via the virtualiser port.

Before the packet is transferred to the destination port, the ACL list for the
transmitting client is checked to ensure the client has permission to
communicate with the receiver. If the permission check fails, the packet is
immediately dropped and returned to the sender.

Once it has been determined that the transmission is permitted, the capacity of
the destination port is checked (see [here](#queue-capacity-checks)). If the
destination port is not at capacity the packet is placed in its Rx queue.
Otherwise, the packet will be dropped and returned to the sender.

### Broadcast

When a broadcast packet is transmitted it will be delivered to all ports the
sender has permission to transmit to, so long as those ports have capacity to
receive packets at the time the packet is processed.

The vswitch uses a buffer reference count system internally to determine when a
buffer can be returned to the transmitting client. Each buffer has it's own
 count, which is incremented each time the buffer is forwarded to a port, and
decremented whenever a port returns the buffer. When the count hits zero, the
buffer is returned to the sending port.

Broadcast packets are forwarded to each destination port at the same time with
the exception of the virtualiser port (on systems supporting checksum offload).
This is because the vswitch needs to zero out the packet's checksum fields prior
to it being processed by the NIC, see the section on
[checksumming](#checksumming).

### Queue capacity checks

Internally, the vswitch performs very simple bookkeeping of the outstanding
number of packets which have been forwarded to each port without being returned.
This is to ensure that copy components are not forwarded more packets than they
are designed to handle simultaneously (the capacity of their queues).

The count is incremented every time a packet is transmitted to a destination
port and decremented when the destination port successfully returns the buffer.
The vswitch will not forward more packets than the port's capacity. If the
capacity is reached, packets will be dropped.

### Example operation

The following diagrams demonstrate how the vswitch handles a client broadcast
packet when hardware checksum offload is not enabled. We show what happens when
client0 (or port 0) transmits a broadcast packet:

![Broadcast example, part 1](/docs/network/imgs/vswitch_tx1.svg)

After the buffer is transmitted by client0, the vswitch finds the buffer's
reference count location using the client number and buffer offset. Since this
is client0 transmitting buffer 0, the first slot is used. The reference count is
then incremented twice as the packet is transmitted to the other ports:

![Broadcast example, part 2](/docs/network/imgs/vswitch_tx2.svg)

Client1's Copier dequeues the buffer first, copies it into a local buffer and
enqueues it into the free queue shared with the vswitch. When the vswitch is
eventually notified by client1's copier, it extracts the buffer's owner using
the `oid` field. It can then decremented the buffer's refcount:

![Broadcast example, part 3](/docs/network/imgs/vswitch_tx3.svg)

When the virtualiser processes the vswitch's notification, it will dequeue the
buffer and pass it to the driver:

![Broadcast example, part 4](/docs/network/imgs/vswitch_tx4.svg)

After the driver transmits the buffer it kicks the Tx virtualiser and it in turn
returns the buffer back to the vswitch, effectively decrementing the reference
count:

![Broadcast example, part 5](/docs/network/imgs/vswitch_tx5.svg)

When the reference count drops to 0, the buffer is finally returned back to the
client0 where it can be reused. After this operation no other component of the
system can access the memory behind the descriptor:

![Broadcast example, part 6](/docs/network/imgs/vswitch_tx6.svg)

### Checksumming

All vswitch clients must generate the checksums of outgoing packets if they wish
for them to be correct when received by other vswitch clients. This is in
contrast to when hardware checksum offload is enabled, and the client can safely
leave all checksums empty to be filled by hardware.

In the case where the vswitch is connected to a NIC supporting hardware checksum
offloading vswitch clients must still generate their checksums in software. The
vswitch will then ensure that the checksums are cleared before passing the
packet to the virtualiser port.

Since other vswitch clients must receive packets *with* software generated
checksums, packets are passed to all non-virtualiser destination ports first.
Once the packet has been copied and returned by each port, it's checksums are
zeroed out and it is forwarded to the virtualiser port.

Since the vswitch needs to inspect the checksums of outgoing packets, the Tx
data regions of vswitch clients need to be mapped into the vswitch PD.

## Usage

### sdfgen

To use vswitch component in your system, a few modifications are required to the
`meta.py` and `.mk` files. The `microkit_sdf_gen` tool contains all necessary
machinery to augment the `.system` file for you. First you need to create a
vswitch PD same as you do with other PDs:

```py
vswitch = ProtectionDomain("net_vswitch", "network_vswitch.elf", priority=97)
```

Important caveat is that it's priority has to be higher than clients that are
connected to it to support the PPC functionality.

When you declare your Network subsystem, you must pass in this vswitch PD to the "vswitch" argument:

```py
net_system = Sddf.Net(
	sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx, vswitch=vswitch
)
```

Then, to connect a client to the vswitch, set the vswitch argument to true:

```py
net_system.add_client_with_copier(client0, client0_net_copier, vswitch=True)
```

Then proceed creating your net subsystem as usual, until `net_system.connect()`
is called. You then need to specify your static vswitch ACL rules, which define
which clients can communicate with which (note by default there are *no*
permissions):

```py
# Assume we have clients 0, 1, 2, 3 and a virtualiser V
# ACLs: x -> y : x can talk to y
# 0 -> 1, 2, 3, V
# 1 -> 0, 2, V
# 2 -> 0, 1, V
# 3 -> 0, V
net_system.add_acl_rule(client0, client1, True, True)
net_system.add_acl_rule(client0, client2, True, True)
net_system.add_acl_rule(client0, client3, True, True)
net_system.add_acl_rule(client0, net_virt_tx, True, True)
net_system.add_acl_rule(client1, client2, True, True)
net_system.add_acl_rule(client1, net_virt_tx, True, True)
net_system.add_acl_rule(client2, net_virt_tx, True, True)
net_system.add_acl_rule(client3, net_virt_tx, True, True)
```

Finally, the system can be serialised with
`net_system.serialise_config(output_dir)`.

### Makefiles

Including a vswitch in your subsystem requires the following additional changes
to your makefile (beyond including the network subsystem). Firstly, you must
include the `network_vswitch.elf` elf file as a target of your makefile, and
include it as an argument to the final system image.

Next, you must copy the system configuration data into the vswitch elf file
after the metaprogram has run:
```sh
$(OBJCOPY) --update-section .net_vswitch_config=net_vswitch.data network_vswitch.elf
```

### Protected Procedure Call API

The PPC API (call IDs, arguments, return values) can be found in
[vswitch.h](/include/sddf/network/vswitch.h):

```c
/**
 * Register a client's IP address with the vswitch.
 */
#define VSWITCH_SET_IP_ADDR 0

/**
 * Request a client's vswitch ID and reachable neighbours.
 */
#define VSWITCH_QUERY_STATE 1

/**
 * Request another client's IP address.
 */
#define VSWITCH_REQ_CLIENT 2
```

The three available PPC calls are:
1. Set IP Address: Publish an IP address associated with this port, for other
   clients  to query.
2. Query vswitch state: Return a bitmap of reachable neighbours. Bit(n) is set
   if client n is reachable.
3. Request a vswitch client's IP address: Return the IP address registered by
   client n.

See the vswitch example client [client.c](/examples/vswitch/client.c) for an
example of how to use each of these APIs.

## Limitations

Due to each vswitch client requiring 2 channels with the vswitch, there is a
limitation of 31 vswitch clients per system. This limitation however could
easily be overcome in the future with additional support from Microkit.

Currently we only support one vswitch per net subsystem, as we did not see the
need for chaining multiple vswitches. Isolated subnets are achievable using a
single vswitch with appropriate ACLs.

In the future, support will be added for the modification of ACL rules at
run-time. This will require clients having a notion of a capability over ACLs.
