#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from pathlib import Path
import sys

from ts_ci import (
    matrix_product,
    HardwareBackend,
    TestConfig,
    wait_for_output,
    TestMetadata,
    run_test,
)

sys.path.insert(1, Path(__file__).parents[2].as_posix())
from ci import common, matrix

TEST_MATRIX = matrix_product(
    example=["i2c_bus_scan"],
    board=matrix.EXAMPLES["i2c_bus_scan"]["boards_test"],
    config=matrix.EXAMPLES["i2c_bus_scan"]["configs"],
    build_system=matrix.EXAMPLES["i2c_bus_scan"]["build_systems"],
)


async def test(backend: HardwareBackend, test_config: TestConfig):
    async with asyncio.timeout(60):
        await wait_for_output(backend, b"           	 ... is present!\r\n")


# export
TEST_METADATA = TestMetadata(
    test_fn=test,
    backend_fn=common.backend_fn,
    loader_img_fn=common.loader_img_path,
    no_output_timeout_s=matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S,
)

if __name__ == "__main__":
    run_test(TEST_METADATA, TEST_MATRIX)
