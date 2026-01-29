#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import os
from pathlib import Path
import sys
import importlib

sys.path.insert(1, Path(__file__).parents[1].as_posix())

from ci.lib.runner import ArgparseActionList, TestResults
from ci.common import list_test_cases

EXAMPLES_DIR = Path(__file__).parent / "examples"
EXAMPLES_TO_RUN = sorted(
    [e.removesuffix(".py") for e in os.listdir(EXAMPLES_DIR) if (e.endswith(".py") and e != "__init__.py")]
)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--examples",
        default=set(EXAMPLES_TO_RUN),
        action=ArgparseActionList,
    )
    parser.add_argument(
        "--only-qemu",
        action=argparse.BooleanOptionalAction,
        help="select only QEMU tests",
    )
    args = parser.parse_args()

    examples_to_run = sorted(set(EXAMPLES_TO_RUN) & args.examples)
    if len(examples_to_run) == 0:
        parser.error("no examples passed")

    filter_flags = []
    if args.only_qemu is True:
        filter_flags.append("--only-qemu")
    elif args.only_qemu is False:
        filter_flags.append("--no-only-qemu")

    results: list[TestResults] = []
    for example in examples_to_run:
        # overwrite args to not leak them to tests
        saved_argv = sys.argv
        try:
            sys.argv = [saved_argv[0]]
            mod = importlib.import_module(f"examples.{example}")
            results.append(mod.run_test(args.only_qemu))
        except SystemExit as e:
            if e.code == 2:
                print(f"Skipping {example} (zero selected tests)")
                continue
            raise
        finally:
            sys.argv = saved_argv

    for result in results:
        print(f"==== Results for example: {result.test_name} ====")
        print("==== Passing ====")
        print(list_test_cases(result.passing))
        print("==== Failed =====")
        print(list_test_cases(result.failing))
        if len(result.not_run) != 0:
            print("===== Cancelled (not run) =====")
            print(list_test_cases(result.not_run))
        if len(result.retry_failures) != 0:
            print("===== Transient failures remaining after multiple retries ====")
            print(list_test_cases(result.retry_failures))

