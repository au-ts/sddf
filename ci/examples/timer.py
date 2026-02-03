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
from ci.lib import log
from ci import common, matrix

TEST_MATRIX = matrix_product(
    example=["timer"],
    board=matrix.EXAMPLES["timer"]["boards_test"],
    config=matrix.EXAMPLES["timer"]["configs"],
    build_system=matrix.EXAMPLES["timer"]["build_systems"],
    timeout_s=[matrix.EXAMPLES["timer"]["timeout_s"]],
)

DRIFT_THRESHOLD = 0.05  # 5 percent.
TIME_MEASURE_COUNT = 5
TIME_LENGTH = 1000**3  # 1 second in nanoseconds


async def test(backend: HardwareBackend, test_config: TestConfig):
    await wait_for_output(backend, b"CLIENT|INFO: starting\r\n")

    async with asyncio.timeout(5 + TIME_MEASURE_COUNT):
        await wait_for_output(backend, b"The time now is: ")
        await wait_for_output(backend, b"Setting a time out for 1 second\r\n")

        times: list[int] = []
        for _ in range(TIME_MEASURE_COUNT):
            await wait_for_output(backend, b"Got a timeout!\r\n")
            # "CLIENT|INFO: Now the time (in nanoseconds) is: 1015768000"
            line = await wait_for_output(backend, b"\r\n")
            assert line.startswith(b"CLIENT|INFO: Now the time (in nanoseconds) is: ")
            time = int(
                line.replace(b"CLIENT|INFO: Now the time (in nanoseconds) is: ", b"")
            )
            times.append(time)

    log.info(f"Times: {times}")

    for i in range(1, len(times)):
        delta_ns = times[i] - times[i - 1]
        if abs(delta_ns - TIME_LENGTH) > (DRIFT_THRESHOLD * TIME_LENGTH):
            raise TestFailureException(
                f"time delta between t{i} and t{i-1} of {delta_ns}ns exceeds {DRIFT_THRESHOLD:.0%} threshold"
            )

    log.info(f"Deltas within {DRIFT_THRESHOLD:.0%} threshold")


if __name__ == "__main__":
    run_single_example(
        test,
        TEST_MATRIX,
        common.backend_fn,
    )
