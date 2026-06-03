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
    wait_for_output,
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
    rb"DHCP request finished, IP address for netif client([0-9]+) is: (\d{1,3}(?:\.\d{1,3}){3})"
)

ICMP_RE = re.compile(
    rb"ICMP reply matched on netif client([0-9]+) peer=([0-9]+) seq=([0-9]+) from (\d{1,3}(?:\.\d{1,3}){3})"
)

# Client x can communicate with client y if ACL_MATRIX[x][y] == 1
ACL_MATRIX = [[0, 1, 1, 1], [1, 0, 1, 0], [1, 1, 0, 0], [1, 0, 0, 0]]

def output_complete(client_dhcp: dict[int, str], client_pings: dict[int, list[int]]):
    for i in range(4):
        # Check DHCP has completed
        if i not in client_dhcp or i not in client_pings:
            return False

        # Check the client has pinged all reachable neighbours
        for j in range(4):
            if not ACL_MATRIX[i][j]:
                continue
            if j not in client_pings[i]:
                return False

    return True

async def test(backend: HardwareBackend, test_config: common.TestConfig):

    # Client x's IP = client_dhcp[x]
    client_dhcp = dict()
    # Client x has successfully pinged client_pings[x]
    client_pings = dict()

    async with asyncio.timeout(30):
        while not output_complete(client_dhcp, client_pings):
            line = await wait_for_output(backend, b"\n")
            reset_terminal()

            dhcp_match = DHCP_RE.search(line)
            icmp_match = ICMP_RE.search(line)

            if dhcp_match:
                client_id = int(dhcp_match.group(1).decode())
                client_ip = dhcp_match.group(2).decode()

                if client_id in client_dhcp:
                    raise TestFailureException(
                        f"client{client_id} reported receiving an IP address twice: IP1 = {client_dhcp[client_id]}, IP2 = {client_ip}"
                    )

                client_dhcp[client_id] = client_ip
                log.info(f"client{client_id} IP: {client_ip}")

            elif icmp_match:
                client_id = int(icmp_match.group(1).decode())
                peer_id = int(icmp_match.group(2).decode())
                peer_ip = icmp_match.group(4).decode()

                # Sanity check IP addresses
                if client_id not in client_dhcp:
                    raise TestFailureException(
                        f"client{client_id} reported pinging peer{peer_id} before receiving an IP address"
                    )
                elif peer_id not in client_dhcp:
                    raise TestFailureException(
                        f"client{client_id} reported pinging peer{peer_id} on ip {peer_ip} before the peer received an IP address"
                    )
                elif peer_ip != client_dhcp[peer_id]:
                    raise TestFailureException(
                        f"client{client_id} reported peer{peer_id} IP = {peer_ip}, should be {client_dhcp[peer_id]}"
                    )

                # Log successful ping echo
                if client_id not in client_pings:
                    client_pings[client_id] = [peer_id]
                else:
                    if peer_id in client_pings[client_id]:
                        raise TestFailureException(
                            f"client{client_id} reported pinging peer{peer_id} twice"
                        )
                    client_pings[client_id].append(peer_id)

                log.info(
                    f"client{client_id} ({client_dhcp[client_id]}) pinged client{peer_id} ({peer_ip}) and received response"
                )

            continue

# export
TEST_CASES = matrix.generate_example_test_cases(
    "vswitch",
    matrix.EXAMPLES["vswitch"],
    test_fn=test,
    backend_fn=backend_fn,
    no_output_timeout_s=matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S,
)

if __name__ == "__main__":
    common.run_tests(TEST_CASES)
