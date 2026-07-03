#!/usr/bin/env python3
# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from pathlib import Path
import sys

from ts_ci import (
    log,
    wait_for_output,
    TestFailureException,
    HardwareBackend,
)

sys.path.insert(1, Path(__file__).parents[2].as_posix())
from ci import common, matrix

DRIFT_THRESHOLD = 0.05  # 5 percent.
TIME_MEASURE_COUNT = 5
TIME_LENGTH = 1000**3  # 1 second in nanoseconds


async def test(backend: HardwareBackend, test_config: common.TestConfig):
    await wait_for_output(backend, b"Read successfully!\r\n")

    async with asyncio.timeout(5 + TIME_MEASURE_COUNT):
        await wait_for_output(backend, b"Inst. valid: 1")


# export
TEST_CASES = matrix.generate_example_test_cases(
    "tmu",
    matrix.EXAMPLES["tmu"],
    test_fn=test,
    backend_fn=common.backend_fn,
    no_output_timeout_s=matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S,
)


if __name__ == "__main__":
    common.run_tests(TEST_CASES)
