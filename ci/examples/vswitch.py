#!/usr/bin/env python3
# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
import re
from pathlib import Path
import sys
from dataclasses import dataclass

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ts_ci import (
    log,
    reset_terminal,
    HardwareBackend,
    QemuBackend,
    TestFailureException,
)

from ci import common, matrix

def backend_fn(test_config: common.TestConfig, loader_img: Path) -> HardwareBackend:
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
			"-netdev", "user,id=netdev0"
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
    ip: str

@dataclass(frozen=True)
class IcmpEvent:
    peer: list[str]
    ip: list[str]

class EventCollector:
    def __init__(self):
        self.dhcp: dict[str, DhcpEvent] = {}
        self.icmp: dict[str, IcmpEvent] = {}

    def feed_line(self, line: bytes) -> None:
        match = DHCP_RE.search(line)
        if match:
            client = match.group(1).decode()
            ip = match.group(2).decode()
            self.dhcp[client] = DhcpEvent(ip)

            reset_terminal()
            log.info(f"{client} IP: {ip}")
            return

        match = ICMP_RE.search(line)
        if match:
            client = match.group(1).decode()
            peer = match.group(2).decode()
            ip = match.group(4).decode()
            if client in self.icmp.keys():
                self.icmp[client].peer.append(peer)
                self.icmp[client].ip.append(ip)
            else:
                self.icmp[client] = IcmpEvent([peer], [ip])
            log.info(f"{client} ({self.dhcp[client].ip}) pinged client{peer} ({ip}) and received response")
            return

    def done(self) -> bool:
        return {"client0", "client1", "client2", "client3"} <= self.dhcp.keys() and \
               {"client0", "client1", "client2", "client3"} <= self.icmp.keys() and \
               len(self.icmp["client0"].peer) == 3 and \
               len(self.icmp["client1"].peer) == 2 and \
               len(self.icmp["client2"].peer) == 2 and \
               len(self.icmp["client3"].peer) == 1


async def collect_until_done(backend: HardwareBackend, timeout_s: float) -> EventCollector:
    collector = EventCollector()

    async with asyncio.timeout(timeout_s):
        while not collector.done():
            line = await backend.output_stream.readline()
            collector.feed_line(line)

    return collector


async def test(backend: HardwareBackend, test_config: TestConfig):
    collector = await collect_until_done(backend, 20.0)

    ACL_MATRIX = [
        [0, 1, 1, 1],
        [1, 0, 1, 0],
        [1, 1, 0, 0],
        [1, 0, 0, 0]
    ]

    for i in range(4):

        tx_client = "client" + str(i)
        for j in range(4):
            if not ACL_MATRIX[i][j]:
                continue

            rx_peer = str(j)
            rx_client = "client" + rx_peer

            if rx_peer not in collector.icmp[tx_client].peer:
                raise TestFailureException(
                    f"{tx_client} should receive ping reply from peer {rx_client}, nothing reported"
                )

            idx = collector.icmp[tx_client].peer.index(rx_peer)

            if collector.icmp[tx_client].ip[idx] != collector.dhcp[rx_client].ip:
                raise TestFailureException(
                    f"{tx_client} should report peer {rx_client} IP {collector.dhcp[rx_client].ip}, got {collector.icmp[tx_client].ip[idx]}"
                )

# export
TEST_CASES = matrix.generate_example_test_cases(
    "vswitch",
    {
        "configs": ["release"],
        "build_systems": ["make"],
        # One for each driver
        "boards": [
            "imx8mm_evk",
            "imx8mq_evk",
            "imx8mp_evk",
            "imx8mp_iotgate",
            "maaxboard",
            "odroidc2",
            "odroidc4",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "rock3b",
            "rpi4b_1gb",
            "star64",
            "x86_64_generic",
        ],
        "tests_exclude": [
            # not in machine queue
            {"board": "imx8mp_evk"},
            {"board": "rock3b"},
        ],
    },
    test_fn=test,
    backend_fn=backend_fn,
    no_output_timeout_s=matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S,
)

if __name__ == "__main__":
    common.run_tests(TEST_CASES)
