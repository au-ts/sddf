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
import contextlib
from datetime import datetime
import itertools
from pathlib import Path
import time
from typing import Literal, Optional, Awaitable, Tuple

from . import log
from .backends import (
    HardwareBackend,
    TestRetryException,
    TestFailureException,
    reset_terminal,
    log_output_to_file,
    TeeOut,
    OUTPUT,
)
from ci.common import TestConfig, loader_img_path

type TestFunction = Callable[[HardwareBackend, TestConfig], Awaitable[None]]
type BackendFunction = Callable[[TestConfig, Path], HardwareBackend]


# Task to monitor for inactivity
async def _watch_stdout_inactivity(
    tee: TeeOut, timeout_no_output: float, poll_s: float = 0.5
):
    while True:
        await asyncio.sleep(poll_s)
        if tee.last_write_age_s() >= timeout_no_output:
            raise asyncio.TimeoutError(f"No output for more than {timeout_no_output}s")


async def _run_with_watchdog(
    main: Awaitable[None], tee: TeeOut, timeout_no_output: float
):
    tee.touch()

    async with asyncio.TaskGroup() as tg:
        watchdog_task = tg.create_task(_watch_stdout_inactivity(tee, timeout_no_output))
        try:
            await main
        finally:
            watchdog_task.cancel()


async def runner(
    test: TestFunction,
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


def _list_test_cases(matrix: list[TestConfig]):
    if len(matrix) == 0:
        return "   (none)"

    lines = []
    for example, tests in itertools.groupby(matrix, key=lambda c: c.example):
        lines.append(f"--- Example: {example} ---")

        for board, group in itertools.groupby(tests, key=lambda c: c.board):
            lines.append(
                " - {}: {}".format(
                    board, ", ".join(f"{c.config}/{c.build_system}" for c in group)
                )
            )

    return "\n".join(lines)


def _subset_test_matrix(
    matrix: list[TestConfig], filters: argparse.Namespace
) -> list[TestConfig]:
    def filter_check(test_config):
        implies = lambda a, b: not a or b
        return all(
            [
                (test_config.example in filters.examples),
                (test_config.board in filters.boards),
                (test_config.config in filters.configs),
                (test_config.build_system in filters.build_systems),
                (implies(filters.only_qemu is True, test_config.is_qemu())),
                (implies(filters.only_qemu is False, not test_config.is_qemu())),
            ]
        )

    return list(filter(filter_check, matrix))


ResultKind = Literal["pass", "fail", "not_run", "retry", "interrupted"]


def run_test_config(
    test_config: TestConfig,
    test_fn: TestFunction,
    backend_fn: BackendFunction,
    logs_dir: Optional[Path] = None,
    loader_img_fn: Optional[Path] = None,
) -> ResultKind:

    loader_img = loader_img_fn or loader_img_path(test_config)
    backend = backend_fn(test_config, loader_img)

    if logs_dir:
        log_file = (
            logs_dir
            / test_config.example
            / test_config.board
            / test_config.config
            / test_config.build_system
            / f"{datetime.now().strftime('%Y-%m-%d_%H.%M.%S')}.log"
        )
        log_file.parent.mkdir(parents=True, exist_ok=True)
        log_file_cm = log_output_to_file(log_file)
    else:
        log_file_cm = contextlib.nullcontext()

    try:
        try:
            with log_file_cm:
                asyncio.run(
                    _run_with_watchdog(
                        runner(test_fn, backend, test_config),
                        OUTPUT,
                        test_config.timeout_s,
                    )
                )
        except* asyncio.TimeoutError as eg:
            # turn ExceptionGroup into a plain TimeoutError
            raise asyncio.TimeoutError(str(eg.exceptions[0])) from None
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


def parse_arguments(
    parser: argparse.ArgumentParser, matrix: list[TestConfig]
) -> Tuple[argparse.Namespace, argparse.Namespace]:
    filters = parser.add_argument_group(title="filters")
    filters.add_argument(
        "--examples",
        default={test.example for test in matrix},
        action=ArgparseActionList,
    )
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
    return (args, filters_args)


def refine_matrix(
    parser: argparse.ArgumentParser,
    args: argparse.Namespace,
    filters_args: argparse.Namespace,
    matrix: list[TestConfig],
) -> list[TestConfig]:
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
        quit(0)

    for test_config in matrix:
        loader_img = loader_img_path(test_config)
        assert loader_img.exists(), f"loader image file {loader_img} does not exist"

    return matrix


def execute_tests(
    matrix: list[TestConfig],
    test_fns: dict[str, TestFunction],
    backend_fns: dict[str, BackendFunction],
    args: argparse.Namespace,
):
    assert len(matrix) > 0, "Test list is empty."

    test_results: dict[TestConfig, ResultKind] = {}
    do_retries = False
    retry_queue: list[TestConfig] = []

    for test_config in matrix:
        test_fn = test_fns[test_config.example]
        backend_fn = backend_fns[test_config.example]

        fmt = f"{test_config.example} on {test_config.board} ({test_config.config}, built with {test_config.build_system})"
        log.group_start("Running " + fmt)
        result = run_test_config(
            test_config,
            test_fn,
            backend_fn,
            args.logs_dir,
            args.override_image,
        )
        log.group_end("Finished running " + fmt)

        test_results[test_config] = result

        if result == "interrupted" or (result != "pass" and args.fast_fail):
            do_retries = False
            break
        elif result == "retry":
            do_retries = True
            retry_queue.append(test_config)

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

            for test_config in retry_queue:
                test_fn = test_fns[test_config.example]
                backend_fn = backend_fns[test_config.example]

                fmt = f"{test_config.example} on {test_config.board} ({test_config.config}, built with {test_config.build_system})"
                log.group_start("Running " + fmt)
                result = run_test_config(
                    test_config,
                    test_fn,
                    backend_fn,
                    args.logs_dir,
                    args.override_image,
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


def run_all_examples(
    matrix: list[TestConfig],
    test_fns: dict[str, TestFunction],
    backend_fns: dict[str, BackendFunction],
):
    parser = argparse.ArgumentParser(
        description="Run all examples passed to this script"
    )
    args, filters_args = parse_arguments(parser, matrix)

    refined_matrix = refine_matrix(parser, args, filters_args, matrix)

    execute_tests(refined_matrix, test_fns, backend_fns, args)


def run_single_example(
    test_fn: TestFunction,
    matrix: list[TestConfig],
    backend_fn: BackendFunction,
):
    """
    test should raise an exception on failure.
    matrix is the set of supported test configs for this test.
    """
    parser = argparse.ArgumentParser(description="Run a single example")
    args, filters_args = parse_arguments(parser, matrix)

    refined_matrix = refine_matrix(parser, args, filters_args, matrix)

    execute_tests(
        refined_matrix,
        {refined_matrix[0].example: test_fn},
        {refined_matrix[0].example: backend_fn},
        args,
    )
