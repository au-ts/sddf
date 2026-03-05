#!/usr/bin/env python3
# Copyright 2025, UNSW
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
    await wait_for_output(backend, b"CLIENT|INFO: starting\r\n")

    async with asyncio.timeout(5 + TIME_MEASURE_COUNT):
        await wait_for_output(backend, b"The time was is: ")
        await wait_for_output(backend, b"Set a time out for 1 second\r\n")

        times: list[int] = []
        for _ in range(TIME_MEASURE_COUNT):
            await wait_for_output(backend, b"Got a timeout!\r\n")
            # "CLIENT|INFO: The time (in nanoseconds) was: 1015768000"
            line = await wait_for_output(backend, b"\r\n")
            assert line.startswith(b"CLIENT|INFO: The time (in nanoseconds) was: ")
            time = int(
                line.replace(b"CLIENT|INFO: The time (in nanoseconds) was: ", b"")
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


# export
TEST_CASES = matrix.generate_example_test_cases(
    "timer",
    matrix.EXAMPLES["timer"],
    test_fn=test,
    backend_fn=common.backend_fn,
    no_output_timeout_s=matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S,
)


if __name__ == "__main__":
    common.run_tests(TEST_CASES)
