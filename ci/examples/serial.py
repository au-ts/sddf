#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from pathlib import Path
import sys

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci.lib.backends import *
from ci.lib.runner import run_single_example, matrix_product
from ci.common import TestConfig
from ci import common, matrix

TEST_MATRIX = matrix_product(
    example=["serial"],
    board=matrix.EXAMPLES["serial"]["boards_test"],
    config=matrix.EXAMPLES["serial"]["configs"],
    build_system=matrix.EXAMPLES["serial"]["build_systems"],
    timeout_s=[matrix.EXAMPLES["serial"]["timeout_s"]],
)

ANSI_RED = b"\x1b[31m"
ANSI_GREEN = b"\x1b[32m"
ANSI_RESET = b"\x1b[0m"


def colour_number(num: bytes, colour: bytes) -> bytes:
    out = b""
    for c in num:
        out += colour + bytes([c]) + ANSI_RESET
    return out


async def test(backend: HardwareBackend, test_config: TestConfig):
    # TODO: We really need some kind of colour (de)multiplexer....

    async with asyncio.timeout(10):
        await wait_for_output(backend, b"Begin input\r\n")
        await wait_for_output(backend, b"Please give me character!\r\n")
        await wait_for_output(backend, b"Please give me character!\r\n")
        await wait_for_output(backend, ANSI_RESET)

        await send_input(backend, b"1234567890")
        await expect_output(backend, colour_number(b"1234567890", ANSI_RED))
        await wait_for_output(
            backend, b"client0 has received 10 characters so far!\r\n"
        )
        await wait_for_output(backend, ANSI_RESET)

        # Switch to client 1.
        await send_input(backend, b"\x1c1\r")
        # TODO: ???
        if test_config.config == "debug":
            await expect_output(backend, b"VIRT_RX|LOG: switching to client 1\r\n")

        await send_input(backend, b"1234567890")
        await expect_output(backend, colour_number(b"1234567890", ANSI_GREEN))
        await wait_for_output(
            backend, b"client1 has received 10 characters so far!\r\n"
        )


if __name__ == "__main__":
    run_single_example(
        test,
        TEST_MATRIX,
        common.backend_fn,
    )
