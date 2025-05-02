#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

"""
Runner (CLI) script for running the hardware tests automagically.
This includes automatic, interactive tests using our "Machine Queue" or within
QEMU.
"""

import argparse
import asyncio
from collections.abc import Awaitable, Callable
from dataclasses import dataclass
import itertools
import os
from pathlib import Path
import time
from typing import Literal

from .backends import (
    HardwareBackend,
    LockedBoardException,
    TestFailureException,
    reset_terminal,
)

# For Github Actions etc.
IS_CI = bool(os.environ.get("CI"))

TEST_TIMEOUT = 60 * 60  # 60 min
LOCK_RETRY_COUNT = 3
# this is between each run over the lock failure tests; not per test.
# prefer increase the retry count over this
LOCK_RETRY_DELAY = 60  # 1 min


@dataclass(order=True, frozen=True)
class TestConfig:
    board: str
    config: str
    build_system: str = "make"

    def is_qemu(self):
        return self.board.startswith("qemu")


async def runner(
    test: Callable[[HardwareBackend, TestConfig], Awaitable[None]],
    backend: HardwareBackend,
    test_config: TestConfig,
):
    await backend.start()
    try:
        async with asyncio.timeout(TEST_TIMEOUT):
            await test(backend, test_config)

    except (EOFError, asyncio.IncompleteReadError):
        raise TestFailureException("EOF when reading from backend stream")
    finally:
        reset_terminal()
        await backend.stop()


def matrix_product(**items):
    assert set(items.keys()) <= set(
        TestConfig.__dataclass_fields__.keys()
    ), "keys subset of config fields"

    return [
        TestConfig(**dict(zip(items.keys(), fields)))
        for fields in itertools.product(*items.values())
    ]


class _ListArg(argparse.Action):
    def __init__(
        self,
        option_strings,
        dest,
        default=None,
    ):
        _option_strings = []
        for option_string in option_strings:
            _option_strings.append(option_string)

            if option_string.startswith("--"):
                option_string = "--exclude-" + option_string[2:]
                _option_strings.append(option_string)

        if not isinstance(default, set):
            raise TypeError(f"default must be a set, got {type(default)}")

        super().__init__(
            option_strings=_option_strings,
            dest=dest,
            default=default,
            # can't use choices as this restricts to single items
            # TODO oops: no verification that the argument is valid
            #            without choices....
            metavar="{" + ",".join(sorted(default)) + "}",
        )

        self.kind: Literal["additive", "subtractive"] | None = None

    def __call__(self, parser, namespace, values: str, option_string: str): # type: ignore
        values_set = set(values.split(","))
        if option_string and option_string.startswith("--exclude"):
            kind = "subtractive"
            values_set = self.default - values_set
        else:
            kind = "additive"

        if self.kind is None:
            self.kind = kind

        if self.kind != kind:
            raise argparse.ArgumentError(
                self,
                "cannot use exclude and non-exclude flags together".format(
                    option_string
                ),
            )

        setattr(namespace, self.dest, values_set)


def _subset_test_matrix(
    matrix: list[TestConfig], filters: argparse.Namespace
) -> list[TestConfig]:
    def filter_check(test_config):
        implies = lambda a, b: not a or b
        return all(
            [
                (test_config.board in filters.boards),
                (test_config.config in filters.configs),
                (test_config.build_system in filters.build_systems),
                (implies(filters.only_qemu, test_config.is_qemu())),
            ]
        )

    return list(filter(filter_check, matrix))


def list_test_cases(matrix: list[TestConfig]):
    if len(matrix) == 0:
        return "   (none)"

    lines = []
    for board, group in itertools.groupby(matrix, key=lambda c: c.board):
        lines.append(
            " - {}: {}".format(
                board, ", ".join(f"{c.config}/{c.build_system}" for c in group)
            )
        )

    return "\n".join(lines)


def log_test_start(name: str):
    if IS_CI:
        print(f"::group::{name}")
    else:
        print(name)


def log_test_end():
    if IS_CI:
        print(f"::endgroup::")

    print()


ResultKind = Literal["pass", "fail", "not_run", "lock_failure", "interrupted"]


def run_test_config(
    test_name: str,
    test_config: TestConfig,
    test_fn: Callable[[HardwareBackend, TestConfig], Awaitable[None]],
    backend_fn: Callable[[TestConfig, Path], HardwareBackend],
    loader_img_fn: Callable[[str, TestConfig], Path],
) -> ResultKind:

    loader_img = loader_img_fn(test_name, test_config)
    backend = backend_fn(test_config, loader_img)

    try:
        asyncio.run(runner(test_fn, backend, test_config))
    except TestFailureException as e:
        print("Test failed:", e)
        return "fail"
    except TimeoutError as e:
        print("Test timed out")
        return "fail"
    except LockedBoardException as e:
        print(e)
        return "lock_failure"
    except KeyboardInterrupt:
        print("Tests cancelled (SIGINT)")
        return "interrupted"

    print("Test passed")
    return "pass"


def cli(
    test_name: str,
    test_fn: Callable[[HardwareBackend, TestConfig], Awaitable[None]],
    matrix: list[TestConfig],
    backend_fn: Callable[[TestConfig, Path], HardwareBackend],
    loader_img_fn: Callable[[str, TestConfig], Path],
):
    """
    test should raise an exception on failure.
    matrix is the set of supported test configs for this test.
    """
    parser = argparse.ArgumentParser(description=__doc__)

    filters = parser.add_argument_group(title="filters")
    filters.add_argument(
        "--boards", default={test.board for test in matrix}, action=_ListArg
    )
    filters.add_argument(
        "--configs", default={test.config for test in matrix}, action=_ListArg
    )
    filters.add_argument(
        "--build-systems",
        default={test.build_system for test in matrix},
        action=_ListArg,
    )
    filters.add_argument(
        "--only-qemu", action="store_true", help="select only QEMU tests"
    )

    parser.add_argument(
        "--single",
        action="store_true",
        help="only run the single test selected, failing if the filters applied select more than one test",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="instead of running tests, show what would have been run",
    )
    parser.add_argument(
        "--fast-fail",
        action="store_true",
        help="fail on first test failure",
    )
    parser.add_argument(
        "--override-backend",
        action="store_true",
        help="force the use of a specific backend to run the test. requires --single",
    )

    args = parser.parse_args()

    filters_args = argparse.Namespace(
        **{a.dest: getattr(args, a.dest) for a in filters._group_actions}
    )

    matrix = sorted(_subset_test_matrix(matrix, filters_args))
    if len(matrix) == 0:
        parser.error("applied filters result in zero selected tests")

    if args.single and len(matrix) != 1:
        parser.error(
            "requested --single but applied filters generated multiple cases: \n"
            + list_test_cases(matrix)
        )

    if args.override_backend:
        if not args.single:
            parser.error("requested --override-backend but --single not specified")

        assert False, "TODO"

    if args.dry_run:
        print("Would run the following test cases:")
        print(list_test_cases(matrix))
        return

    for test_config in matrix:
        loader_img = loader_img_fn(test_name, test_config)
        assert loader_img.exists(), f"loader image file {loader_img} does not exist"

    test_results: dict[TestConfig, ResultKind] = {}
    run_lock_retries = False
    lock_failure_retry_queue: list[TestConfig] = []

    for test_config in matrix:
        log_test_start(
            f"Running {test_name} on {test_config.board} ({test_config.config}, built with {test_config.build_system})"
        )
        result = run_test_config(
            test_name, test_config, test_fn, backend_fn, loader_img_fn
        )
        log_test_end()

        test_results[test_config] = result

        if result == "interrupted" or (result != "pass" and args.fast_fail):
            run_lock_retries = False
            break
        elif result == "lock_failure":
            run_lock_retries = True
            lock_failure_retry_queue.append(test_config)

    if run_lock_retries:
        for retry in range(LOCK_RETRY_COUNT):
            if len(lock_failure_retry_queue) == 0:
                break

            next_retry_queue: list[TestConfig] = []
            print(
                f"Retrying (retry {retry + 1}/{LOCK_RETRY_COUNT}); waiting for {LOCK_RETRY_DELAY}s"
            )
            time.sleep(LOCK_RETRY_DELAY)

            for test_config in lock_failure_retry_queue:
                log_test_start(
                    f"Retrying {test_name} on {test_config.board} ({test_config.config}, built with {test_config.build_system})"
                )
                result = run_test_config(
                    test_name, test_config, test_fn, backend_fn, loader_img_fn
                )
                log_test_end()

                test_results[test_config] = result

                if result == "lock_failure":
                    next_retry_queue.append(test_config)

            lock_failure_retry_queue = next_retry_queue

    passing, failing, lock_failures, not_run = [], [], [], []
    for test_config in matrix:
        result = test_results.get(test_config, "not_run")
        if result == "pass":
            passing.append(test_config)
        elif result == "fail" or result == "interrupted":
            failing.append(test_config)
        elif result == "lock_failure":
            lock_failures.append(test_config)
        elif result == "not_run":
            not_run.append(test_config)
        else:
            assert False, "impossible"

    print("==== Passing ====")
    print(list_test_cases(passing))
    print("==== Failed =====")
    print(list_test_cases(failing))
    if len(not_run) != 0:
        print("===== Cancelled (not run) =====")
        print(list_test_cases(not_run))
    if len(lock_failures) != 0:
        print("===== Failed to acquire locks ====")
        print(list_test_cases(lock_failures))

    if len(passing) != len(matrix):
        quit(1)
