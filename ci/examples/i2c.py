#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from pathlib import Path
import sys

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci.lib.backends import *
from ci.lib.runner import TestConfig, cli, matrix_product

TEST_MATRIX = matrix_product(
    board=("odroidc4",),
    # only prints output in debug mode
    config=("debug",),
)


def backend_fn(backend: HardwareBackend, test_config: TestConfig) -> HardwareBackend:
    if isinstance(backend, MachineQueueBackend) and test_config.board == "odroidc4":
        # Only odroidc4_2 is connected to the I²C tests
        backend.board = "odroidc4_2"

    return backend


async def test(backend: HardwareBackend, test_config: TestConfig):
    await wait_for_output(backend, b"Driver initialised.\r\n")

    async with asyncio.timeout(30):
        await wait_for_output(
            backend, b"Set Date and Time on DS3231 to: 31-12-23 23:59:42 (Sunday)\r\n"
        )

        # It should take us less than 20 sec before it becomes Monday.
        await wait_for_output(backend, b"Date and Time: 01-01-24 00:00:00 (Monday)\r\n")


if __name__ == "__main__":
    cli("i2c", test, TEST_MATRIX, backend_fn)
