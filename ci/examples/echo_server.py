#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
import functools
import re
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory
import sys
import tempfile

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci.hardware_backend import *
from ci.runner import TestConfig, cli, matrix_product

TEST_MATRIX = matrix_product(
    board=(
        "imx8mm_evk",
        "imx8mq_evk",
        "imx8mp_evk",
        "maaxboard",
        "odroidc2",
        "odroidc4",
        "qemu_virt_aarch64",
    ),
    config=("debug", "release", "benchmark"),
)


def backend_fn(backend: HardwareBackend, test_config: TestConfig) -> HardwareBackend:
    if isinstance(backend, QemuBackend):
        # fmt: off
        backend.invocation_args.extend([
			"-global", "virtio-mmio.force-legacy=false",
			"-device", "virtio-net-device,netdev=netdev0",
			"-netdev", "user,id=netdev0,hostfwd=tcp::1236-:1236,hostfwd=tcp::1237-:1237,hostfwd=udp::1235-:1235",
        ])
        # fmt: on

    return backend


async def test(backend: HardwareBackend, test_config: TestConfig):
    await wait_for_output(backend, b"echo client starting")
    await wait_for_output(backend, b"echo client starting")

    async with asyncio.timeout(20):
        await wait_for_output(backend, b"DHCP request finished")
        dhcp_client1 = await wait_for_output(backend, b"\r\n")
        await wait_for_output(backend, b"DHCP request finished")
        dhcp_client0 = await wait_for_output(backend, b"\r\n")

        dhcp_client1, dhcp_client0 = (
            (dhcp_client1, dhcp_client0)
            if b"client1" in dhcp_client1
            else (dhcp_client0, dhcp_client1)
        )

        try:
            # fmt: off
            ip1 = re.search(rb"\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}", dhcp_client1).group(0).decode()
            ip0 = re.search(rb"\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}", dhcp_client0).group(0).decode()
            # fmt: on
        except IndexError:
            raise TestFailureException(
                "could not find IP address in DHCP request result"
            )

        reset_terminal()
        print(f"client IPs: client1={ip1}, client0={ip0}")


if __name__ == "__main__":
    cli("echo_server", test, TEST_MATRIX, backend_fn)
