#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
import re
from pathlib import Path
import sys

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci.lib.backends import *
from ci.lib.runner import TestConfig, cli, matrix_product
from ci.lib import log
from ci import common, matrix

TEST_MATRIX = matrix_product(
    board=matrix.EXAMPLES["echo_server"]["boards_test"],
    config=matrix.EXAMPLES["echo_server"]["configs"],
    build_system=matrix.EXAMPLES["echo_server"]["build_systems"],
)


def backend_fn(test_config: TestConfig, loader_img: Path) -> HardwareBackend:
    backend = common.backend_fn(test_config, loader_img)

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
        log.info(f"client IPs: client0={ip0}, client1={ip1}")

    # Now let's do the actual benchmark!

    assert test_config.config == "benchmark"

    bench_backend = IpBenchQueueBackend(
        ["vb04", "vb06"],
        Path(__file__).parent / "benchmark.py",
        target_ip=ip0,
        throughputs=[10000000, 20000000],
        samples=100,
    )

    # XXX: I probably want to redesign the CI so that output is always printed
    #      at the moment I'm sort of working around the fact that I only get
    #      output printed while waiting, which means can't easily output
    #      2 streams at once.

    try:
        await bench_backend.start()
        ANSI_RESET = b"\x1b[0m"
        for _ in bench_backend.throughputs:
            await wait_for_output(backend, b"Utilization connection established!\r\n" + ANSI_RESET)
            await wait_for_output(bench_backend, b"[send_command] : START\n")
            await wait_for_output(backend, b"client0 measurement starting...\r\n" + ANSI_RESET)
            # TODO: ipbench print useful string out after the results.
            await asyncio.gather(
                wait_for_output(backend, b"client0 measurement finished \r\n" + ANSI_RESET),
                wait_for_output(bench_backend, b"[send_command] : STOP\n")
            )

            # All PDs + two initial ones. TODO: Make the bench print out a good string at the end to avoid this.
            for _ in range(12):
                await wait_for_output(backend, b"}\r\n")

            reset_terminal()

        await wait_for_output(bench_backend, b"iq.sh runner is done\n")

    # XXX: This doesn't work with ctrl+c the locks don't get released...
    finally:
        # XXX: When stopping, always print out the rest of the output?
        await bench_backend.stop()


if __name__ == "__main__":
    cli("echo_server", test, TEST_MATRIX, backend_fn, common.loader_img_path)
