#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(1, Path(__file__).parents[1].as_posix())

from ci.lib.runner import ArgparseActionList

EXAMPLES_DIR = Path(__file__).parent / "examples"
EXAMPLES_TO_RUN = sorted(
    [e.removesuffix(".py") for e in os.listdir(EXAMPLES_DIR) if e.endswith(".py")]
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

    results: dict[str, bool] = {}
    try:
        for example in examples_to_run:
            proc = subprocess.run([EXAMPLES_DIR / (example + ".py"), *filter_flags])
            if proc.returncode != 0:
                if proc.returncode == 2:
                    # this is the case when it doesn't support some of our filters
                    continue

                results[example] = False
                continue

            results[example] = True
    except KeyboardInterrupt:
        results[example] = False  # type: ignore
        print("\nSIGINT, exiting...")

    passed = [e for e in examples_to_run if results.get(e) is True]
    failed = [e for e in examples_to_run if results.get(e) is False]
    not_run = [e for e in examples_to_run if results.get(e) is None]
    print("==== Passing ====")
    for example in passed:
        print(f"- {example}")
    if len(passed) == 0:
        print("  (none)")
    print("==== Failed =====")
    for example in failed:
        print(f"- {example}")
    if len(failed) == 0:
        print("  (none)")

    if len(not_run) != 0:
        print("===== Not run =====")
        for example in not_run:
            print(f"- {example}")

    if len(failed) != 0:
        quit(1)
