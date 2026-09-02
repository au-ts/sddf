<!--
    Copyright 2026, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# VSwitch Example

This example demonstrates how to include a vswitch component in your subsystem.
The example has a similar set up to the [echo
server](/examples/echo_server/README.md) example, however has four network
clients which are all clients of the vswitch.

The demo has two parts:

1. All four clients obtain an IP address with DHCP, discover their reachable
   neighbours, and send each neighbour one ICMP request.
2. An orchestrator PD (`vswitch_orchestrator`) toggles the port forwarding ACL
   rules between Client 0 and Client 1, but it will wait until the first part
   of the demo completes.
   Clients 0 and 1 notify orchestrator PD after they have completed neighbour
   discovery. The orchestrator then toggles the ACL between ports 0 and 1 every
   five seconds. Client 0 sends an ICMP probe to client 1 once per second,
   so replies appear only while the runtime ACL permits this traffic.

The system architecture of a vswitch client system is described
[here](/docs/network/vswitch.md).

## Building

Follow the same building instructions as the [echo server
example](/examples/echo_server/README.md#building).

## Running

After loading the image, you should see the following logs:

```
DHCP request finished, IP address for netif client3 is: 10.0.2.15
DHCP request finished, IP address for netif client2 is: 10.0.2.16
DHCP request finished, IP address for netif client1 is: 10.0.2.17
DHCP request finished, IP address for netif client0 is: 10.0.2.18
```

This indicates that each client has successfully completed DHCP and printed its
IP address. Clients will then register their IP addresses with the vswitch,
request their reachable neighbours, request the IP address of each reachable
neighbour, then try to ping each neighbour once. Once clients 0 and 1 have
both completed this process, the ACL test begins.

The orchestrator also reports each runtime ACL update, for example:

```
vSwitch ACL: port 0 <-> port 1 is disabled
vSwitch ACL: port 0 <-> port 1 is enabled
ICMP reply matched on netif client0 peer=1 seq=18 from 10.0.2.17
```

Here is the output from client 0, which has permissions to contact each of it's
three neighbours:

```
ICMP dst = 10.0.2.17 raw=0x1102000a
Sent the ICMP for netif client0 success: 1 # Sending to client 1
ICMP dst = 10.0.2.16 raw=0x1002000a
Sent the ICMP for netif client0 success: 1 # Sending to client 2
ICMP dst = 10.0.2.15 raw=0x0f02000a
Sent the ICMP for netif client0 success: 1 # Sending to client 3
ICMP reply matched on netif client0 peer=3 seq=1 from 10.0.2.15 # Receive response from client 3
ICMP reply matched on netif client0 peer=2 seq=1 from 10.0.2.16 # Receive response from client 2
ICMP reply matched on netif client0 peer=1 seq=1 from 10.0.2.17 # Receive response from client 1
```
