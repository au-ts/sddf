#!/usr/bin/env python3
# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from pathlib import Path
import sys

from ts_ci import (
    wait_for_output,
    HardwareBackend,
)

sys.path.insert(1, Path(__file__).parents[2].as_posix())
from ci import common, matrix


async def test(backend: HardwareBackend, test_config: common.TestConfig):
    async with asyncio.timeout(60):
        await wait_for_output(backend, b"INA219|INFO: 	Power= 179\r\n")


# export
TEST_CASES = matrix.generate_example_test_cases(
    "ina219",
    matrix.EXAMPLES["ina219"],
    test_fn=test,
    backend_fn=common.backend_fn,
    no_output_timeout_s=matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S,
)


if __name__ == "__main__":
    common.run_tests(TEST_CASES)
