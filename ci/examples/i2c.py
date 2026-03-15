#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from pathlib import Path
import sys

from ts_ci import (
    TestConfig,
    HardwareBackend,
    matrix_product,
    MachineQueueBackend,
    wait_for_output,
    TestMetadata,
    run_test,
)

sys.path.insert(1, Path(__file__).parents[2].as_posix())
from ci import common, matrix

TEST_MATRIX = matrix.generate_example_test_matrix("i2c", matrix.EXAMPLES["i2c"])


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


# export
TEST_METADATA = TestMetadata(
    test_fn=test,
    backend_fn=backend_fn,
    loader_img_fn=common.loader_img_path,
    no_output_timeout_s=matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S,
)

if __name__ == "__main__":
    run_test(TEST_METADATA, TEST_MATRIX)
