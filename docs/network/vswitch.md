<!--
    Copyright 2026, UNSW
    SPDX-License-Identifier: BSD-2-Clause
-->

# VSwitch component

The vswitch is an optional component of the sDDF networking stack. It models a
physical Ethernet switch with the ability to send and receive packets to all
network clients connected to it.

The vswitch supports a simple Access Control List (ACL) scheme in the form of
allow lists stating which ports may communicate with each other. ACLs are
configured statically when the system is generated and may be updated at
run-time by authorised clients. Communication can be uni- or bi-directional.

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

Vswitch clients must be connected to the vswitch for:
(1) both transmission and reception, or (2) ACL rules update, or both (1) and (2).
When (1), the transmit queues of vswitch clients are connected to the vswitch
component, as are the receive queues of the vswitch client's Copy component.
Thus all packets sent and received by vswitch client pass through the vswitch
component. When (2), a PPC channel between the client and the vSwitch is established.

An example system with two vswitch clients and one non-vswitch client is shown
in the following figure:
![VSwitch in the system](/docs/network/imgs/vswitch.svg)

The abstraction the vswitch uses for a data-plane connection (a pair of Rx and
Tx queues for transmission and reception) is a *port*. A port can correspond to
no more than a client PD. Clients that serve only for the purpose of ACL rules
update have no corresponding vSwitch port. See the following definition from the
[network config file](/include/sddf/network/config.h):

```c
typedef struct net_vswitch_port_config {
    net_connection_resource_t rx; // Rx queue of the port
    net_connection_resource_t tx; // Tx queue of the port
    region_resource_t tx_data; // Tx data region of the port
    mac_addr_t mac_addr; // MAC address of the port (ignored if virtualiser port)
    uint64_t initial_acl; // ACL state installed when the vSwitch starts
} net_vswitch_port_config_t;
```

The final port in the vswitch's port list (port at index `config.num_ports - 1`) is
the virtualiser port - the port which holds the connections with the Rx and Tx
virtualisers. In the virtualiser port, the Rx and Tx connections are reversed.
The Rx virtualiser is connected to the `tx` queue, and the Tx virtualiser is
connected to the `rx` queue. This allows the vswitch component to handle the
system receiving packets as the virtualiser port *transmitting* packets, and the
system transmitting packets as the virtualiser port *receiving* packets.

A port in a vSwitch and a client to a vSwitch are represented separately.
The abstraction of a vSwitch client contains a `connection` and a `acl_set_permission`.
The `connection` can represent either a port or a PPC channel (by using upper bits in
the data word to denote whether the lower bits represent the ID of a port or a PPC
channel). Such an abstraction identifies the connection through which a PD may transmit
network pacakages, issue PPCs, and records whether it may update ACLs:

```c
typedef uint8_t net_vswitch_client_connection_t;

typedef struct net_vswitch_client_config {
    net_vswitch_client_connection_t connection;
    bool acl_set_permission;
} net_vswitch_client_config_t;
```

In implementation, a client connection is a tagged byte. Its upper two bits
identify the connection type and its lower six bits contain either a port ID
or a direct PPC channel ID. The two supported client roles are:

* A **port-backed client** owns a port and its queues for data-plane. Its PPC
  channel is obtained from the port's Tx connection. It may optionally be
  authorised to update ACLs.
* A **channel-backed client** stores a PPC channel directly and has no port. An
  ACL-only client uses this form, consumes no queues or data regions, and can
  only use the ACL update operation.

Registering a data-plane client as an ACL client sets `acl_set_permission` on
its existing port-backed client entry. It does not allocate another client
entry, channel, or port. The virtualiser port has no corresponding client entry
because it does not issue PPCs.

### ACL representation

Each port's ACL state is a bitmap of the destination ports to which it may
transmit. Therefore, bit `d` in `ports[s].initial_acl` initially permits traffic
from source port `s` to destination port `d`. The vSwitch copies this bitmap
into its mutable ACL state during initialisation.

When a client needs to update an ACL rule in either a uni- or bi-directional way,
it should provide two bitmaps following such an ACL representation:

* The **outward** bitmap for port `p` replaces `p`'s own ACL state because it
  describes the destinations to which `p` may transmit.
* The **inward** bitmap for port `p` updates bit `p` in every source port's ACL
  state because it describes the sources which may transmit to `p`.

Passing `UINT64_MAX` for either bitmap leaves that direction unchanged. Bitmap
bits beyond the configured port range are ignored.

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

To create an ACL-only client, register the PD with `add_acl_client`:

```py
net_system.add_acl_client(acl_manager)
```

This creates a PPC channel to the vswitch without allocating a port, Copier,
queues, or data regions. To grant ACL-set permission to an existing data-plane
client, register the same PD with both methods:

```py
net_system.add_client_with_copier(client0, client0_net_copier, vswitch=True)
net_system.add_acl_client(client0)
```

The sdfgen tool recognises the overlap, creates one port-backed client entry, and
reuses the data-plane client's PPC channel. A standalone ACL manager instead
gets a channel-backed client entry. The sdfgen tool accounts for both forms when
checking the Microkit channel-ID limit.

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

/**
 * Set a port's allowed incoming and outgoing traffic.
 */
#define VSWITCH_SET_ACL 3
```

The four available PPC calls are:

1. Set IP Address: Publish an IP address associated with this port, for other
   clients to query.
2. Query vswitch state: Return a bitmap of reachable neighbours. Bit(n) is set
   if client n is reachable.
3. Request a vswitch client's IP address: Return the IP address registered by
   client n.
4. Set ACL: Replace the inward and/or outward ACL bitmap of a target port. This
   call requires ACL-set permission and may be used by either an authorised
   data-plane client or an ACL-only client.

The first three operations require the caller to own a data-plane port. An
ACL-only client receives `VSWITCH_ERR_INVALID_OPERATION` if it invokes one of
them.
`VSWITCH_SET_ACL` returns `VSWITCH_ERR_ACL_PERMISSION_DENIED` when the
caller lacks ACL-set permission and `VSWITCH_ERR_ACL_INVALID_PORT` when the
target port is outside the configured range.

An ACL update passes the following message registers:

```c
sddf_set_mr(VSWITCH_ACL_PORT, target_port);
sddf_set_mr(VSWITCH_ACL_IW_BITMAP, inward_bitmap);
sddf_set_mr(VSWITCH_ACL_OW_BITMAP, outward_bitmap);
sddf_ppcall(vswitch_channel,
            seL4_MessageInfo_new(VSWITCH_SET_ACL, 0, 0,
                                 VSWITCH_ACL_NUM_ARGS));
```

See the vswitch example client [client.c](/examples/vswitch/client.c) for an
example of the data-plane APIs, and
[orchestrator.c](/examples/vswitch/orchestrator.c) for an ACL-only client which
updates ACLs at run-time.

## Limitations

Each port uses two channel IDs and each ACL-only client uses one. The
virtualiser port also uses two. Microkit provides 62 channel IDs per PD, so all
channels allocated to the vSwitch PD must fit within that limit. Granting ACL
permission to a data-plane client does not allocate another channel. This
limitation could be overcome in the future with additional Microkit support.

Currently we only support one vswitch per net subsystem, as we did not see the
need for chaining multiple vswitches. Isolated subnets are achievable using a
single vswitch with appropriate ACLs.
