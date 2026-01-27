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
from contextlib import nullcontext
from dataclasses import dataclass
from datetime import datetime
import itertools
import os
from pathlib import Path
import time
from typing import Literal, Optional
import concurrent.futures

from . import log
from .backends import (
    HardwareBackend,
    TestRetryException,
    TestFailureException,
    reset_terminal,
    log_output_to_file,
    OUTPUT,
)


@dataclass(order=True, frozen=True)
class TestConfig:
    board: str
    config: str
    build_system: str

    def is_qemu(self):
        return self.board.startswith("qemu")


async def runner(
    test: Callable[[HardwareBackend, TestConfig], Awaitable[None]],
    backend: HardwareBackend,
    test_config: TestConfig,
):
    try:
        await backend.start()
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


class ArgparseActionList(argparse.Action):
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

    def __call__(self, parser, namespace, values: str, option_string: str):  # type: ignore
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
                (implies(filters.only_qemu is True, test_config.is_qemu())),
                (implies(filters.only_qemu is False, not test_config.is_qemu())),
            ]
        )

    return list(filter(filter_check, matrix))


def _list_test_cases(matrix: list[TestConfig]):
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


ResultKind = Literal["pass", "fail", "not_run", "retry", "interrupted"]


def run_test_config(
    test_name: str,
    test_config: TestConfig,
    test_fn: Callable[[HardwareBackend, TestConfig], Awaitable[None]],
    backend_fn: Callable[[TestConfig, Path], HardwareBackend],
    loader_img_fn: Callable[[str, TestConfig], Path],
    logs_dir: Optional[Path] = None,
) -> ResultKind:

    loader_img = loader_img_fn(test_name, test_config)
    backend = backend_fn(test_config, loader_img)

    if logs_dir:
        log_file = (
            logs_dir
            / test_name
            / test_config.board
            / test_config.config
            / test_config.build_system
            / f"{datetime.now().strftime('%Y-%m-%d_%H.%M.%S')}.log"
        )
        log_file.parent.mkdir(parents=True, exist_ok=True)
        log_file_cm = log_output_to_file(log_file)
    else:
        log_file_cm = nullcontext()

    try:
        with log_file_cm:
            asyncio.run(runner(test_fn, backend, test_config))

    except TestFailureException as e:
        log.error(f"Test failed: {e}")
        return "fail"
    except (TimeoutError, asyncio.TimeoutError) as e:
        log.error("Test timed out")
        return "fail"
    except TestRetryException as e:
        log.info(f"Retrying later due to transient failure: {e}")
        return "retry"
    except KeyboardInterrupt:
        log.info("Tests cancelled (SIGINT)")
        return "interrupted"

    log.info(f"Test passed")
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
        "--boards", default={test.board for test in matrix}, action=ArgparseActionList
    )
    filters.add_argument(
        "--configs", default={test.config for test in matrix}, action=ArgparseActionList
    )
    filters.add_argument(
        "--build-systems",
        default={test.build_system for test in matrix},
        action=ArgparseActionList,
    )
    filters.add_argument(
        "--only-qemu",
        action=argparse.BooleanOptionalAction,
        help="select only QEMU tests",
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
    parser.add_argument(
        "--override-image",
        type=Path,
        help="force the use of a specific loader.img file to run the test. requires --single",
    )
    parser.add_argument(
        "--logs-dir",
        type=Path,
        default=Path("ci_logs"),
        action=argparse.BooleanOptionalAction,
        help="save output to a log directory",
    )
    parser.add_argument(
        "--retry-count",
        type=int,
        default=15,
        help=(
            "number of times to retry tests due to transient failures (e.g. lock failures). "
            "prefer increasing this over the delay between retries"
        ),
    )
    parser.add_argument(
        "--retry-delay",
        type=int,
        default=60,
        help=(
            "time (seconds) to delay between transient failure retries. this is between ALL tests, not individual ones. "
            "think of this as the polling delay between checking locks"
        ),
    )

    args = parser.parse_args()

    filters_args = argparse.Namespace(
        **{a.dest: getattr(args, a.dest) for a in filters._group_actions}
    )

    matrix = sorted(_subset_test_matrix(matrix, filters_args))
    if len(matrix) == 0:
        parser.error("applied filters result in zero selected tests")

    if loader_img := args.override_image:
        if not args.single:
            parser.error("requested --override-image but --single not specified")

        # Remove config and build system from the path as we pass the board path.
        # But we still want to make the user specify the board.
        matrix = sorted(
            set(
                TestConfig(board=test.board, config="custom", build_system="custom")
                for test in matrix
            )
        )

        loader_img_fn = lambda n, c: loader_img

    if args.single and len(matrix) != 1:
        parser.error(
            "requested --single but applied filters generated multiple cases: \n"
            + _list_test_cases(matrix)
        )

    if args.override_backend:
        if not args.single:
            parser.error("requested --override-backend but --single not specified")

        assert False, "TODO"

    if args.dry_run:
        print("Would run the following test cases:")
        print(_list_test_cases(matrix))
        return

    for test_config in matrix:
        loader_img = loader_img_fn(test_name, test_config)
        assert loader_img.exists(), f"loader image file {loader_img} does not exist"

    test_results: dict[TestConfig, ResultKind] = {}
    do_retries = False
    retry_queue: list[TestConfig] = []

    ## We can run tests in parallel if they are on different boards, we cannot run debug/release on the same board
    ## Logging has to be handled properly - we cannot interleave logs
    with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
        # submit jobs
        futures_to_testruns = {}
        for test_config in matrix:
            future_to_testrun = executor.submit(run_test_config, test_name, test_config, test_fn, backend_fn, loader_img_fn, args.logs_dir)
            futures_to_testruns[test_config] = future_to_testrun

        # read futures
        for future in concurrent.futures.as_completed(futures_to_testruns):
            result = "fail"
            test_config = futures_to_testruns[future]
            try:
                result = future.result()
            except Exception as exc:
                print('%r generated an exception: %s' % ("Blabla", exc))
            else:
                if result == "interrupted" or (result != "pass" and args.fast_fail):
                    do_retries = False
                    break
                elif result == "retry":
                    do_retries = True
                    retry_queue.append(test_config)

            test_results[test_config] = result

    if do_retries:
        for retry in range(args.retry_count):
            if len(retry_queue) == 0:
                break

            next_retry_queue: list[TestConfig] = []
            log.info(
                f"Retrying (retry {retry + 1}/{args.retry_count}); waiting for {args.retry_delay}s"
            )
            try:
                time.sleep(args.retry_delay)
            except KeyboardInterrupt:
                break

            ## Run retries in parallel as well

            for test_config in retry_queue:
                fmt = f"{test_name} on {test_config.board} ({test_config.config}, built with {test_config.build_system})"
                log.group_start("Running " + fmt)
                result = run_test_config(
                    test_name,
                    test_config,
                    test_fn,
                    backend_fn,
                    loader_img_fn,
                    args.logs_dir,
                )
                log.group_end("Finished running " + fmt)

                test_results[test_config] = result

                if result == "retry":
                    next_retry_queue.append(test_config)

            retry_queue = next_retry_queue

    passing, failing, retry_failures, not_run = [], [], [], []
    for test_config in matrix:
        result = test_results.get(test_config, "not_run")
        if result == "pass":
            passing.append(test_config)
        elif result == "fail" or result == "interrupted":
            failing.append(test_config)
        elif result == "retry":
            retry_failures.append(test_config)
        elif result == "not_run":
            not_run.append(test_config)
        else:
            assert False, "impossible"

    print("==== Passing ====")
    print(_list_test_cases(passing))
    print("==== Failed =====")
    print(_list_test_cases(failing))
    if len(not_run) != 0:
        print("===== Cancelled (not run) =====")
        print(_list_test_cases(not_run))
    if len(retry_failures) != 0:
        print("===== Transient failures remaining after multiple retries ====")
        print(_list_test_cases(retry_failures))

    if len(passing) != len(matrix):
        quit(1)
