#!/usr/bin/env python3
# Copyright 2026, UNSW
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
    IpBenchQueueBackend,
    MachineQueueBackend,
    TestFailureException,
)

SDDF = Path(__file__).parents[2]
sys.path.insert(1, SDDF.as_posix())
from ci import common, matrix


def backend_fn(test_config: common.TestConfig, loader_img: Path) -> HardwareBackend:
    backend = common.backend_fn(test_config, loader_img)

    assert isinstance(
        backend, MachineQueueBackend
    ), "for now we only support machine queue run examples here"

    assert test_config.config == "benchmark", "only benchmark-mode benchmark allowed"

    return IpBenchQueueBackend(
        "vb_group",
        backend,
        SDDF / "examples" / "echo_server" / "scripts" / "benchmark.py",
    )


async def test(iq_backend: IpBenchQueueBackend, test_config: common.TestConfig):
    mq_backend = iq_backend.mq_backend

    async with asyncio.timeout(20):
        await wait_for_output(mq_backend, b"DHCP request finished")
        dhcp_client1 = await wait_for_output(mq_backend, b"\r\n")
        await wait_for_output(mq_backend, b"DHCP request finished")
        dhcp_client0 = await wait_for_output(mq_backend, b"\r\n")

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

    # Now let's do the actual benchmark!

    target_ip = ip0

    # fmt: off
    await iq_backend.begin_benchmark(
        target_ip,
        "--clients", "vb01", "vb02", "vb03", "vb04",
    )
    # fmt: on

    await wait_for_output(iq_backend, b"Running benchmarks for:\n    throughputs: ")
    throughputs = await wait_for_output(iq_backend, b"\n    packet sizes: ")
    packet_sizes = await wait_for_output(iq_backend, b"\n")
    throughputs = throughputs.decode().split(", ")
    packet_sizes = packet_sizes.decode().split(", ")

    async with asyncio.timeout(60):
        await wait_for_output(
            iq_backend,
            b"[IpbenchTestTarget:__init__] : client " + target_ip.encode() + b"\n",
        )

    ANSI_RESET = b"\x1b[0m"
    for _ in throughputs:
        await wait_for_output(
            mq_backend, b"Utilization connection established!\r\n" + ANSI_RESET
        )
        await wait_for_output(iq_backend, b"[send_command] : START\n")
        await wait_for_output(
            mq_backend, b"client0 measurement starting...\r\n" + ANSI_RESET
        )
        await asyncio.gather(
            wait_for_output(
                mq_backend, b"client0 measurement finished \r\n" + ANSI_RESET
            ),
            wait_for_output(iq_backend, b"[send_command] : STOP\n"),
        )

        async with asyncio.timeout(20):
            # no ANSI_RESET here because followed by output...
            await wait_for_output(mq_backend, b"BENCHMARK: begin output\r\n")
            # but an ANSI_RESET here because switches client
            await wait_for_output(mq_backend, b"BENCHMARK: end output\r\n" + ANSI_RESET)

        reset_terminal()

    await wait_for_output(iq_backend, b"iq.sh runner is done\n")


# export
TEST_CASES = matrix.generate_example_test_cases(
    "echo_server",
    {
        "configs": ["benchmark"],
        "build_systems": ["make"],
        # One for each driver
        "boards": [
            # dwmac-5.10a driver
            "star64",
            # genet driver
            "rpi4b_1gb"
            # imx driver
            "maaxboard",
            # meson driver
            "odroidc4",
        ],
        "tests_exclude": [],
    },
    test_fn=test,
    backend_fn=backend_fn,
    # Benchmark can take much longer.
    no_output_timeout_s=360,
)


if __name__ == "__main__":
    common.run_tests(TEST_CASES)
