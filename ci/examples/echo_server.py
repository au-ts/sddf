#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
import re
from pathlib import Path
import sys

from ts_ci import (
    log,
    matrix_product,
    reset_terminal,
    wait_for_output,
    HardwareBackend,
    QemuBackend,
    TestFailureException,
)

sys.path.insert(1, Path(__file__).parents[2].as_posix())
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
			"-netdev", "user,id=netdev0," +
                       "hostfwd=udp::1235-10.0.2.15:1235,hostfwd=tcp::1236-10.0.2.15:1236,hostfwd=tcp::1237-10.0.2.15:1237," +
                       "hostfwd=udp::1238-10.0.2.16:1235,hostfwd=tcp::1239-10.0.2.16:1236,hostfwd=tcp::1240-10.0.2.16:1237",
        ])
        # fmt: on

    return backend


async def test(backend: HardwareBackend, test_config: common.TestConfig):
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
            ip1 = re.search(rb"\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}", dhcp_client1).group(0).decode() # type: ignore
            ip0 = re.search(rb"\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}", dhcp_client0).group(0).decode() # type: ignore
            # fmt: on
        except (IndexError, AttributeError):
            raise TestFailureException(
                "could not find IP address in DHCP request result"
            )

        reset_terminal()
        log.info(f"client IPs: client1={ip1}, client0={ip0}")


# export
TEST_CASES = matrix.generate_example_test_cases(
    "echo_server",
    matrix.EXAMPLES["echo_server"],
    test_fn=test,
    backend_fn=backend_fn,
    no_output_timeout_s=matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S,
)


if __name__ == "__main__":
    common.run_tests(TEST_CASES)
