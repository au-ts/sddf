#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import os
from pathlib import Path
import subprocess
import sys
from dataclasses import dataclass

sys.path.insert(1, Path(__file__).parents[1].as_posix())

from ci.lib.runner import ArgparseActionList

EXAMPLES_DIR = Path(__file__).parent / "examples"
EXAMPLES_TO_RUN = sorted(
    [e.removesuffix(".py") for e in os.listdir(EXAMPLES_DIR) if e.endswith(".py")]
)


@dataclass
class JobState:
    test: str
    board: str
    config: str
    build_system: str
    status: str = "PENDING"  # PENDING | PASS | FAIL


def parse_dry_run_matrix(dry_run_output: str) -> list[tuple[str, str, str]]:
    """
    Parses runner.py's _list_test_cases output, e.g.
      - qemu_virt: debug/make, release/zig
    Returns list of (board, config, build_system).
    """
    items: list[tuple[str, str, str]] = []
    for raw in dry_run_output.splitlines():
        line = raw.strip()
        if not line.startswith("- "):
            continue
        # "- <board>: <cfg>/<sys>, <cfg>/<sys>"
        try:
            board_part, rest = line[2:].split(":", 1)
        except ValueError:
            continue
        board = board_part.strip()
        rest = rest.strip()
        if not rest:
            continue
        for token in rest.split(","):
            token = token.strip()
            if not token:
                continue
            # "<config>/<build_system>"
            if "/" not in token:
                continue
            config, build_system = token.split("/", 1)
            items.append((board, config.strip(), build_system.strip()))
    return items


def discover_jobs_for_example(
    example: str, filter_flags: list[str]
) -> list[tuple[str, str, str]] | None:
    """
    Returns list of (board, config, build_system) or None if example can't be run due to filters.
    """
    cmd = [str(EXAMPLES_DIR / f"{example}.py"), "--dry-run", *filter_flags]
    proc = subprocess.run(cmd, text=True, capture_output=True)
    if proc.returncode == 2:
        # doesn't support some filters, skip
        return None
    if proc.returncode != 0:
        # dry run failed
        raise RuntimeError(
            f"Dry-run failed for {example}:\n--- stdout ---\n{proc.stdout}\n--- stderr ---\n{proc.stderr}"
        )

    return parse_dry_run_matrix(proc.stdout)


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

    state_by_test: dict[str, list[JobState]] = {}
    jobs_in_order: list[JobState] = []
    failed = 0

    # Discover full matrix
    skipped_examples: set[str] = set()
    for example in examples_to_run:
        discovered = discover_jobs_for_example(example, filter_flags)
        if discovered is None:
            skipped_examples.add(example)
            continue
        state_by_test.setdefault(example, [])
        for board, config, build_system in discovered:
            js = JobState(example, board, config, build_system)
            state_by_test[example].append(js)
            jobs_in_order.append(js)

    try:
        # Run each selected config as a single subprocess job TODO: later add parallel running like seL4 does
        for js in jobs_in_order:
            js.status = "RUNNING"

            cmd = [
                str(EXAMPLES_DIR / f"{js.test}.py"),
                "--single",
                "--boards",
                js.board,
                "--configs",
                js.config,
                "--build-systems",
                js.build_system,
                *filter_flags,
            ]

            try:
                subprocess.run(cmd, check=True)
                js.status = "PASS"
            except subprocess.CalledProcessError as e:
                js.status = "FAIL"
                failed += 1
    except KeyboardInterrupt:
        failed += 1
        print("\nSIGINT, exiting...")

    # Print failures sorted by example
    for example, jobs in state_by_test.items():
        passing = [job for job in jobs if job.status == "PASS"]
        failing = [job for job in jobs if job.status == "FAIL"]
        print(f"==== Example: {example} ====")
        print("==== Passing ====")
        for job in passing:
            print(f"- {job.board}: {job.build_system} {job.config}")
        print("==== Failed =====")
        for job in failing:
            print(f"- {job.board}: {job.build_system} {job.config}")

    if len(skipped_examples) > 0:
        print("==== Skipped examples: ====")
        for skipped in skipped_examples:
            print(f"{skipped}")

    if failed > 0:
        print(f"==== Total failed: {failed} ====")
        quit(1)
