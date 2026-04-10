#!/usr/bin/env python3
# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
import re
from pathlib import Path
import sys
from dataclasses import dataclass

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci.lib.backends import *
from ci.lib.runner import run_single_example, matrix_product
from ci.common import TestConfig
from ci.matrix import NO_OUTPUT_DEFAULT_TIMEOUT_S
from ci.lib import log
from ci import common, matrix

TEST_MATRIX = matrix_product(
    example=["vswitch"],
    board=matrix.EXAMPLES["vswitch"]["boards_test"],
    config=matrix.EXAMPLES["vswitch"]["configs"],
    build_system=matrix.EXAMPLES["vswitch"]["build_systems"],
    timeout_s=[NO_OUTPUT_DEFAULT_TIMEOUT_S],
)


#TODO: share this code with echo server?
## Also we can share parts of it with echo_server as it extends it
def backend_fn(test_config: TestConfig, loader_img: Path) -> HardwareBackend:
    backend = common.backend_fn(test_config, loader_img)

    if isinstance(backend, QemuBackend):
        if test_config.board == "x86_64_generic":
            virtio_device = "virtio-net-pci,netdev=netdev0,addr=0x2.0"
        else:
            virtio_device = "virtio-net-device,netdev=netdev0,bus=virtio-mmio-bus.0"
        # fmt: off
        backend.invocation_args.extend([
			"-global", "virtio-mmio.force-legacy=false",
			"-device",  virtio_device,
			"-netdev", "user,id=netdev0," +
                       "hostfwd=udp::1235-10.0.2.15:1235,hostfwd=tcp::1236-10.0.2.15:1236,hostfwd=tcp::1237-10.0.2.15:1237," +
                       "hostfwd=udp::1238-10.0.2.16:1235,hostfwd=tcp::1239-10.0.2.16:1236,hostfwd=tcp::1240-10.0.2.16:1237",
        ])
        # fmt: on

    return backend

DHCP_RE = re.compile(
    rb"DHCP request finished, IP address for netif (client[0-9]+) is: (\d{1,3}(?:\.\d{1,3}){3})"
)

ICMP_RE = re.compile(
    rb"ICMP reply matched on netif (client[0-9]+) peer=([0-9]+) seq=([0-9]+) from (\d{1,3}(?:\.\d{1,3}){3})"
)

@dataclass(frozen=True)
class DhcpEvent:
    client: str
    ip: str

@dataclass(frozen=True)
class IcmpEvent:
    client: str
    peer: str
    ip: str

class EventCollector:
    def __init__(self):
        self.dhcp: dict[str, DhcpEvent] = {}
        self.icmp: dict[str, IcmpEvent] = {}

    def feed_line(self, line: bytes) -> None:
        match = DHCP_RE.search(line)
        if match:
            client = match.group(1).decode()
            ip = match.group(2).decode()
            self.dhcp[client] = DhcpEvent(client, ip)

            reset_terminal()
            log.info(f"{client} IP: {ip}")
            return

        match = ICMP_RE.search(line)
        if match:
            client = match.group(1).decode()
            peer = match.group(2).decode()
            ip = match.group(4).decode()
            self.icmp[client] = IcmpEvent(client, peer, ip)
            return

    def done(self) -> bool:
        return {"client0", "client1"} <= self.dhcp.keys() and {"client0", "client1"} <= self.icmp.keys()


async def collect_until_done(backend: HardwareBackend, timeout_s: float) -> EventCollector:
    collector = EventCollector()

    async with asyncio.timeout(timeout_s):
        while not collector.done():
            line = await backend.output_stream.readline()
            OUTPUT.write(line)
            collector.feed_line(line)

    return collector


async def test(backend: HardwareBackend, test_config: TestConfig):
    collector = await collect_until_done(backend, 20.0)

    dhcp0 = collector.dhcp["client0"].ip
    dhcp1 = collector.dhcp["client1"].ip

    icmp0 = collector.icmp["client0"].ip
    icmp1 = collector.icmp["client1"].ip

    if icmp0 != dhcp1:
        raise TestFailureException(
            f"client0 should report peer client1 IP {dhcp1}, got {icmp0}"
        )

    if icmp1 != dhcp0:
        raise TestFailureException(
            f"client1 should report peer client0 IP {dhcp0}, got {icmp1}"
        )

if __name__ == "__main__":
    run_single_example(
        test,
        TEST_MATRIX,
        backend_fn,
    )
