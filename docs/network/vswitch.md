<!--
    Copyright 2026, UNSW
    SPDX-License-Identifier: BSD-2-Clause
-->

# VSwitch component

## Purpose

The VSwitch component is an optional component of the sDDF networking stack. It models a physical Ethernet switch with the ability to send and receive packets to all PDs connected to the vswitch. A PD is connected as a pair of transmit and receive components (a Client and a Copier, or a Tx and Rx virtualiser). This pair is called a *port*. It supports a simple Access Control Lists scheme in a form of allow lists stating which PDs can communicate with each other. The communication, therefore, can be uni or bi-directional.

A typical system comprising of a vswitch and a few clients is visible in the figure below:
![VSwitch in the system](/docs/network/imgs/vswitch.svg)

With a VSwitch one can create multiple isolated networks in a system, maintaining the principle of Confidentiality from the CIA triade. Clients never receive buffers that were not addressed to them, and even if some client performs a broadcast transmission, the ACL will filter out the destinations that are not permitted from this port.

## Operation

The VSwitch supports up to 62 clients when a virtualiser is connected and 63 when it's not. Connection of a pair of virtualisers allows for interacting with the external world and if that's not needed the vswitch works akin to intranet. When packets arrive at an ingress port, they are inspected against an internal mapping of MAC addresses behind each other port. If a port matching the requested MAC is not found, the packet is assumed to be dedicated towards external world and is routed via the virtualiser. In case there is no virtualiser connected and no MAC is matched the packet is dropped.

In case the packet is a broadcast packet, it will be delivered to all ports that can accept it according to the ACLs and their respective occupancy. Broadcasting is internally done by keeping a reference count of the number of ports a packet has been handed over to. It is decremented every time the buffer stamped as originating from that port is returned. This is achieved by keeping a special bit field in `net_buffer_desc_t` struct - `oid` - owner's id.

Internally, vswitch performs very simple bookkeeping of the number of packets it has already transmitted to a given destination port as to not flood it with packets if a client cannot keep up. The count is incremented every time a packet is transmitted to a destination port and decremented when the destination port successfully returns the buffer.

A diagram describing a simple scenario where client0 is broadcasting a packet is attached below to illustrate that better:

![Broadcast example, part 1](/docs/network/imgs/vswitch_tx1.svg)

After the buffer is transmitted directly from client0, the reference count indexed by this port index and buffer's offset is bumped up to match how many times it was transmitted:

![Broadcast example, part 2](/docs/network/imgs/vswitch_tx2.svg)

Client1's Copier dequeues the buffer first and enqueues it into it's Client's active queue, the buffer is enqueued back into the free queue back to the vswitch and notifies it. vswitch gets the notification and matches the buffer's `oid` against the refcount table and decrements the count corresponding to this buffer's offset:

![Broadcast example, part 3](/docs/network/imgs/vswitch_tx3.svg)

Then, the virtualiser gets the notification and dequeues the buffer. It then enqueues the buffer into the driver. The refcount does not get decremented yet:

![Broadcast example, part 4](/docs/network/imgs/vswitch_tx4.svg)

After the driver transmits the buffer it kicks the Tx virtualiser and it in turn returns the buffer back to the vswitch, effectively decrementing the reference count:

![Broadcast example, part 5](/docs/network/imgs/vswitch_tx5.svg)

When the reference count drops to 0, the buffer is finally returned back to the client0 where it can be reused. After this operation no other component of the system can access the memory behind the descriptor:

![Broadcast example, part 6](/docs/network/imgs/vswitch_tx6.svg)

There is a rare case in which the vswitch is connected to a NIC with hardware offloaded cheksumming and the clients already perform this checksumming (e.g. Linux VMs hosted on `libvmm`). In such case the checksum will be applied twice when transmitted through the Ethernet driver. Although the easiest solution would be to turn off the checksumming for the clients whatsoever, sometimes it's impossible (e.g. Virtio spec allows for [*partial checksumming option*](https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-1970003) but not for disabling it wholly). In such cases vswitch is responsible for clearing the checksum before passing it to virtualisers.

To do this, it needs to modify the packet only when passing it to the virtualiser and since the packet is only a descriptor, it cannot modify the memory until it's **sure** that no other client is referencing it. This requires knowing that all other clients have already returned the buffer containing the packet.

Since vswitch needs to inspect the packets, Tx data regions of its clients have to be mapped into the vswitch PD. Also, the packets are not copied unless they are received by a client's Copier component which is present because the clients are inherently untrusted.

## Usage

### sdfgen

To use vswitch component in your system, a few modifications are required to the `meta.py` and `.mk` files. The `microkit_sdf_gen` tool contains all necessary machinery to augment the `.system` file for you. First you need to create a vswitch PD same as you do with other PDs:
```py
vswitch = ProtectionDomain("net_vswitch", "network_vswitch.elf", priority=97)
```
Important caveat is that it's priority has to be higher than clients that are connected to it if you want to call the IP - related PPCs on it.

The `vswitch` example makes usage of the two Protected Procedure calls, one to report the IP address obtained via DHCP from the server, and other to query IPs of ports connected to the vswitch. This, of course can be extended to the developer's liking as, for example, MAC addresses could be queried, or the ACLs themselves.

Then, connect it to your clients:
```py
net_system.add_client_with_copier(client0, client0_net_copier, vswitch=vswitch)
```
And add it as your child PD:
```py
child_pds = [
  … other pds
  vswitch
]
```
Next, **after** you call `net_system.connect()` and **before** you call `net_system.serialise_config(output_dir)` you need to specify the ACLs that define which PDs can talk to which:
```py
# Assume we have clients 0, 1, 2, 3 and a virtualiser V
# We add ACLs as follows:
# 0 <-> 1, 3, V
# 1 <-> 0, V
# 2 <-> V
# 3 <-> 0, 1, V
net_system.add_acl_rule(client0, client3, vswitch)
net_system.add_acl_rule(client0, net_virt_tx, vswitch)
net_system.add_acl_rule(client1, client0, vswitch)
net_system.add_acl_rule(client1, net_virt_tx, vswitch)
net_system.add_acl_rule(client2, net_virt_tx, vswitch)
net_system.add_acl_rule(client3, client0, vswitch)
net_system.add_acl_rule(client3, client1, vswitch)
net_system.add_acl_rule(client3, net_virt_tx, vswitch)
```

The API `add_acl_rule` also allows unidirectional ACL specification. Such case is presented below:
```py
# Assume we have clients 0, 1 and a virtualiser V
# We add ACLs as follows:
# 0 <-> 1, V
# 1 <-> V
net_system.add_acl_rule(client0, client1, vswitch, True, False)
net_system.add_acl_rule(client0, net_virt_tx, vswitch)
net_system.add_acl_rule(client1, net_virt_tx, vswitch)
```
In such a system `client0` can talk to `client1` and the outside world but `client0` is limited only to communication with the outside world via the virtualiser and cannot talk to `client1`.

### Makefiles

Similarly to other components, the makefiles for any system including vswitch will also have to be modified.

First modification is that since each copier now contains unique mapping of data regions that is patched by the `sdfgen` tool and then copied into the elf sections by `objcopy`, the network_copy elf file itself has to be copied:
```sh
	cp network_copy.elf network_copy0.elf
	cp network_copy.elf network_copy1.elf
```
Patching is done as follows:
```sh
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client0_net_copier.data network_copy0.elf
	$(OBJCOPY) --update-section .net_copy_config=net_copy_client1_net_copier.data network_copy1.elf
```

Next, the vswitch elf file has to be included in the final system image:
```sh
	$(OBJCOPY) --update-section .net_vswitch_config=net_vswitch.data network_vswitch.elf
```

Lastly, remember to add the `network_vswitch.elf` to your list of `IMAGES` so that it will be included in the build.

## Limitations

Right now, the vswitch is limited by the number of PDs that can be connected to it. There is a possibility of extending that in the future but that is at the discretion of Microkit maintainers.

Next limitation is that you can currently have just one vswitch in the system. There is not much sense in having more than one vswitch as you can realize subsequent subnets via ACLs inside a single vswitch. The only foreseeable case for multiple vswitches would be in a system where you have multiple NICs that should serve different clients on different vswitches.

Currently, when the vswitch is overloaded with packets to a destination that cannot accept any more packets, it will simply drop them. It potentially could have an internal "in-flight" queue that it would periodically try re-transmitting instead of dropping.

Due to how some protocols, e.g. ICMP require the destination to be able to reply to the sender, hence uni-directional ACL settings will prevent one side replying and in turn the ICMP echos will never be replied to. Ideally, a switch would allow for such uni-directional communication but it would require more packet inspection and corner cases which would impact the performance.

In a rare case user would like to modify the ACLs during system's runtime, e.g. if a PD is misbehaving and somehow it was caught red-handed, there should be a notion of a *supervisor* PD that would then instruct the vswitch to restrict the offending PD's access to say virtualisers. This is not implemented as such, but would require just minor adjustments to the `protected` entrypoint.

Right now there is an unhandled corner case where the vswitch would be responsible for **adding** a checksum. If 2 clients are communicating via vswitch with the expectation of a checksum being filled in by the HW, it will never be filled because the packet never reaches the Ethernet driver. The vswitch should detect this case and add the checksum.
