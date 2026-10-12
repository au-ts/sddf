#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from pathlib import Path
import sys

from ts_ci import (
    expect_output,
    send_input,
    wait_for_output,
    HardwareBackend,
)

sys.path.insert(1, Path(__file__).parents[2].as_posix())
from ci import common, matrix

ANSI_RED = b"\x1b[31m"
ANSI_GREEN = b"\x1b[32m"
ANSI_RESET = b"\x1b[0m"


def colour_number(num: bytes, colour: bytes) -> bytes:
    out = b""
    for c in num:
        out += colour + bytes([c]) + ANSI_RESET
    return out


async def test(backend: HardwareBackend, test_config: common.TestConfig):
    # TODO: We really need some kind of colour (de)multiplexer....

    async with asyncio.timeout(60):
        await wait_for_output(backend, b"Begin input\r\n")
        await wait_for_output(backend, b"Please give me character!\r\n")
        await wait_for_output(backend, b"Please give me character!\r\n")

        for i in range(100):
            for c in range(2):
                await wait_for_output(backend, ANSI_RESET)

                await send_input(backend, f"\x1c{c}\r".encode())
                # TODO: ???
                if test_config.config == "debug":
                    await expect_output(
                        backend, f"VIRT_RX|LOG: switching to client {c}\r\n".encode()
                    )

                await send_input(backend, b"1234567890")
                await expect_output(
                    backend, colour_number(b"1234567890", [ANSI_RED, ANSI_GREEN][c])
                )
                await wait_for_output(
                    backend,
                    f"client{c} has received {(i + 1) * 10} characters so far!\r\n".encode(),
                )


# export
TEST_CASES = matrix.generate_example_test_cases(
    "serial",
    matrix.EXAMPLES["serial"],
    test_fn=test,
    backend_fn=common.backend_fn,
    no_output_timeout_s=matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S,
)


if __name__ == "__main__":
    common.run_tests(TEST_CASES)
