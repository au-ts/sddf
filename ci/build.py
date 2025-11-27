#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import contextlib
from dataclasses import dataclass
from collections import deque
import time

try:
    from rich.console import Console, Group
    from rich.table import Table
    from rich.panel import Panel
    RICH_OK = True
except Exception:
    RICH_OK = False

sys.path.insert(1, Path(__file__).parents[1].as_posix())

from ci.lib.runner import ArgparseActionList, TestConfig, matrix_product
from ci.lib import log
from ci import common, matrix


@dataclass
class JobState:
    example: str
    board: str
    config: str
    build_system: str
    status: str = "PENDING"  # PENDING | RUNNING | DONE | FAILED


def get_example_dir(example_name: str):
    SDDF = Path(__file__).parents[1]
    return SDDF / "examples" / example_name

def is_ci() -> bool:
    return bool(os.environ.get("CI"))

def render_dashboard(state_by_example: dict[str, list[JobState]]):
    # Rendering with rich
    panels = []
    ## prefer the current sorting?
    for ex in sorted(state_by_example.keys()):
        jobs = state_by_example[ex]
        done = sum(1 for j in jobs if js.status in ("DONE", "FAILED"))
        t = Table(show_header=True, box=None, padding=(0,1))
        t.add_column("board", no_wrap=True)
        t.add_column("config", no_wrap=True)
        t.add_column("sys", no_wrap=True)
        t.add_column("status", no_wrap=True)
        for j in jobs:
            t.add_row(j.board, j.config, j.build_system, j.status)

        panels.append(Panel(t, title=f"{ex} ({done}/{len(jobs)})", border_style="dim"))
    return Group(*panels)

def print_dashboard_plain(state_by_example: dict[str, list[JobState]]):
    for ex in sorted(state_by_example.keys()):
        jobs = state_by_example[ex]
        done = sum(1 for j in jobs if js.status in ("DONE", "FAILED"))
        print(f"{ex} ({done}/{len(jobs)})")
        for j in jobs:
            print(f" {j.board:10} {j.config:10} {j.build_system:4} {j.status}")
        print()

def run_quiet_for_dashboard(cmd, *, cwd=None, env=None, tail_lines=200) -> None:
    # Swallow logs, keep the tail for debugging
    tail = deque(maxlen=tail_lines)
    p = subprocess.Popen(
            cmd,
            cwd=str(cwd) if cwd is not None else None,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
            universal_newlines=True,
    )
    assert p.stdout is not None
    for line in p.stdout:
        tail.append(line.rstrip("\n"))
    rc = p.wait()
    if rc != 0:
        msg = "\n".join(tail)
        raise subprocess.CalledProcessError(rc, cmd, output=msg)


def build_make(args: argparse.Namespace, example_name: str, test_config: TestConfig, dashboard: bool):
    build_dir = common.example_build_path(example_name, test_config)
    example_dir = get_example_dir(example_name)

    cmd = [
            "make",
            f"--jobs={args.num_jobs}",
            f"--directory={example_dir}",
            f"BUILD_DIR={build_dir}",
            f"MICROKIT_SDK={args.microkit_sdk}",
            f"MICROKIT_BOARD={test_config.board}",
            f"MICROKIT_CONFIG={test_config.config}",
    ]
    if dashboard:
        run_quiet_for_dashboard(cmd)
    else:
        subprocess.run(cmd, check=True)


def build_zig(args: argparse.Namespace, example_name: str, test_config: TestConfig, dashboard: bool):
    build_dir = common.example_build_path(example_name, test_config)
    example_dir = get_example_dir(example_name)

    zig_env = os.environ.copy()
    zig_env["ZIG_GLOBAL_CACHE_DIR"] = str(common.CI_BUILD_DIR / "zig-cache")
    zig_env["ZIG_LOCAL_CACHE_DIR"] = str(common.CI_BUILD_DIR / "zig-cache")

    cmd = [
                "zig",
                "build",
                f"-Dsdk={args.microkit_sdk}",
                f"-Dboard={test_config.board}",
                f"-Dconfig={test_config.config}",
                "-p",
                build_dir,
                f"-j{args.num_jobs}",
    ]

    if dashboard:
        run_quiet_for_dashboard(cmd, cwd=example_dir, env=zig_env)
    else:
        with contextlib.chdir(example_dir):
            subprocess.run(
                cmd,
                check=True,
                env=zig_env,
            )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)

    parser.add_argument("microkit_sdk")
    parser.add_argument("num_jobs", nargs="?", type=int, default=os.cpu_count())
    parser.add_argument(
        "--examples",
        default=set(matrix.EXAMPLES.keys()),
        action=ArgparseActionList,
    )
    parser.add_argument(
        "--no-clean",
        action="store_true",
        help="Do not remove any pre-existing CI build directory before building",
    )

    args = parser.parse_args()

    if not args.no_clean:
        try:
            shutil.rmtree(common.CI_BUILD_DIR)
        except FileNotFoundError:
            pass

    dashboard = (not is_ci()) and RICH_OK
    console = Console(stderr=True) if dashboard else None

    state_by_example: dict[str, list[JobState]] = {}
    jobs_in_order: list[tuple[JobState, TestConfig]] = []

    # Prepare the jobs # TODO: this can be later ported to running as well
    for example_name, options in matrix.EXAMPLES.items():
        if example_name not in args.examples:
            continue

        example_matrix = matrix_product(
            board=options["boards_build"],
            config=options["configs"],
            build_system=options["build_systems"],
        )
        state_by_example.setdefault(example_name, [])
        for cfg in example_matrix:
            js = JobState(example_name, cfg.board, cfg.config, cfg.build_system)
            state_by_example[example_name].append(js)
            jobs_in_order.append((js, cfg))

    failed = 0
    last_draw = 0.0

    def draw():
        global last_draw
        if not dashboard:
            return

        now = time.monotonic()
        if now - last_draw < 0.1:
            return
        last_draw = now
        console.clear()
        console.print(render_dashboard(state_by_example))

    draw()
    # Build and optionally draw
    for js, cfg in jobs_in_order:
        js.status = "RUNNING"
        draw()

        try:
            if cfg.build_system == "make":
                build_make(args, js.example, cfg, dashboard)
            elif cfg.build_system == "zig":
                build_zig(args, js.example, cfg, dashboard)
            else:
                raise NotImplementedError(f"unknown build system '{cfg.build_system}'")
            js.status = "DONE"
        except subprocess.CalledProcessError as e:
            js.status = "FAILED"
            failed += 1
            draw()
            # Small backtrace of failing build
            if dashboard:
                console.print("\n[bold red]Build failed (tail):[/bold red]")
                out = getattr(e, "output", "")
                if out:
                    console.print(out)
        draw()

    # Draw static dashboard for CI
    if not dashboard:
        print_dashboard_plain(state_by_example)

    print(f"Failed jobs: {failed}")

