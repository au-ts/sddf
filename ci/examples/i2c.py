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
    example="i2c",
    board=matrix.EXAMPLES["i2c"]["boards_test"],
    config=matrix.EXAMPLES["i2c"]["configs"],
    build_system=matrix.EXAMPLES["i2c"]["build_systems"],
)


def backend_fn(test_config: TestConfig, loader_img: Path) -> HardwareBackend:
    backend = common.backend_fn(test_config, loader_img)

    if isinstance(backend, MachineQueueBackend) and test_config.board == "odroidc4":
        # Only odroidc4_1 is connected to the I²C tests
        backend.boards = ["odroidc4_1"]

    return backend


async def test(backend: HardwareBackend, test_config: TestConfig):
    async with asyncio.timeout(30):
        await wait_for_output(
            backend, b"Set Date and Time on DS3231 to: 31-05-25 23:59:42 (Sunday)\r\n"
        )

        # It should take us less than 20 sec before it becomes Monday.
        await wait_for_output(backend, b"Date and Time: 01-06-25 00:00:00 (Monday)\r\n")


if __name__ == "__main__":
    run_single_example(
        "i2c",
        test,
        TEST_MATRIX,
        backend_fn,
    )
