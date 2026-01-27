#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import os
from collections import deque
from dataclasses import dataclass
from pathlib import Path
import subprocess
import sys
from typing import Optional

sys.path.insert(1, Path(__file__).parents[1].as_posix())

from ci.lib.runner import ArgparseActionList

try:
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    from rich.text import Text
    from rich.live import Live
    RICH_OK = True
except Exception:
    RICH_OK = False

EXAMPLES_DIR = Path(__file__).parent / "examples"
EXAMPLES_TO_RUN = sorted(
    [e.removesuffix(".py") for e in os.listdir(EXAMPLES_DIR) if e.endswith(".py")]
)

def is_ci() -> bool:
    return bool(os.environ.get("CI"))

# ---------------- Dashboard model ----------------

@dataclass
class JobState:
    test: str
    board: str
    config: str
    build_system: str
    status: str = "PENDING"  # PENDING | RUNNING | PASS | FAIL | SKIP
    tail: str = ""           # captured output tail for failures

def _job_color(status: str) -> str:
    if status in ("PENDING", "RUNNING"):
        return "yellow"
    if status == "PASS":
        return "green"
    if status == "FAIL":
        return "red"
    if status == "SKIP":
        return "bright_black"
    return "white"

def _panel_border(jobs: list[JobState]) -> str:
    if any(j.status == "FAIL" for j in jobs):
        return "red"
    if jobs and all(j.status in ("PASS", "SKIP") for j in jobs):
        return "green"
    return "yellow"

def render_dashboard(state_by_test: dict[str, list[JobState]]):
    panels: list[Panel] = []

    for test in sorted(state_by_test.keys()):
        jobs = state_by_test[test]
        done = sum(1 for j in jobs if j.status in ("PASS", "FAIL", "SKIP"))
        total = len(jobs)

        t = Table(show_header=True, box=None, padding=(0, 1))
        t.add_column("board", no_wrap=True)
        t.add_column("config", no_wrap=True)
        t.add_column("sys", no_wrap=True)
        t.add_column("status", no_wrap=True)

        for j in jobs:
            t.add_row(
                j.board,
                j.config,
                j.build_system,
                Text(j.status, style=_job_color(j.status)),
            )

        panels.append(
            Panel(
                t,
                title=f"{test} ({done}/{total})",
                border_style=_panel_border(jobs),
            )
        )

    grid = Table.grid(expand=True)
    grid.add_column(ratio=1)
    grid.add_column(ratio=1)
    grid.add_column(ratio=1)

    for i in range(0, len(panels), 3):
        mid = panels[i + 1] if i + 1 < len(panels) else ""
        right = panels[i + 2] if i + 2 < len(panels) else ""
        grid.add_row(panels[i], mid, right)

    return grid

def print_dashboard_plain(state_by_test: dict[str, list[JobState]]):
    for test in sorted(state_by_test.keys()):
        jobs = state_by_test[test]
        done = sum(1 for j in jobs if j.status in ("PASS", "FAIL", "SKIP"))
        print(f"{test} ({done}/{len(jobs)})")
        for j in jobs:
            print(f"  {j.board:12} {j.config:12} {j.build_system:6} {j.status}")
        print()

# ---------------- Process helpers ----------------

def run_quiet_capture_tail(cmd, *, cwd=None, env=None, tail_lines=200) -> str:
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
    out = "\n".join(tail)
    if rc != 0:
        raise subprocess.CalledProcessError(rc, cmd, output=out)
    return out

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

def discover_jobs_for_example(example: str, filter_flags: list[str]) -> list[tuple[str, str, str]] | None:
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

# ---------------- Main ----------------

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
    parser.add_argument(
        "--dashboard",
        action=argparse.BooleanOptionalAction,
        default=None,
        help="force enable/disable rich dashboard (default: enabled when interactive + rich available)",
    )
    args = parser.parse_args()

    examples_to_run = sorted(set(EXAMPLES_TO_RUN) & args.examples)
    if len(examples_to_run) == 0:
        parser.error("no examples passed")

    filter_flags: list[str] = []
    if args.only_qemu is True:
        filter_flags.append("--only-qemu")

    dashboard = (args.dashboard if args.dashboard is not None else ((not is_ci()) and RICH_OK))

    state_by_test: dict[str, list[JobState]] = {}
    jobs_in_order: list[JobState] = []

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

    live: Optional[Live] = None
    console: Optional[Console] = None
    if dashboard:
        console = Console(stderr=True, force_terminal=True, markup=False)
        live = Live(
            render_dashboard(state_by_test),
            console=console,
            screen=True,
            refresh_per_second=10,
        )
        live.start()

    def draw():
        if live is not None:
            live.update(render_dashboard(state_by_test), refresh=True)

    failed = 0
    try:
        draw()

        # Run each selected config as a single subprocess job (we cannot run examples concurrently as they use the same HW)
        for js in jobs_in_order:
            js.status = "RUNNING"
            draw()

            cmd = [
                str(EXAMPLES_DIR / f"{js.test}.py"),
                "--single",
                "--boards", js.board,
                "--configs", js.config,
                "--build-systems", js.build_system,
                *filter_flags,
            ]

            try:
                if dashboard:
                    _ = run_quiet_capture_tail(cmd)
                else:
                    subprocess.run(cmd, check=True)
                js.status = "PASS"
            except subprocess.CalledProcessError as e:
                js.status = "FAIL"
                failed += 1
                js.tail = getattr(e, "output", "") or ""
                draw()
                if dashboard and console is not None:
                    console.print(f"\n[bold red]{js.test} failed ({js.board} {js.config}/{js.build_system}) tail:[/bold red]")
                    if js.tail:
                        console.print(js.tail, markup=False, highlight=False, soft_wrap=True)

            draw()

    except KeyboardInterrupt:
        if dashboard and console is not None:
            console.print("\n[bold yellow]SIGINT, exiting...[/bold yellow]")
        failed += 1
    finally:
        if live is not None:
            live.stop()

    if not dashboard:
        print_dashboard_plain(state_by_test)

    if skipped_examples:
        print("Skipped examples (filters unsupported):")
        for ex in sorted(skipped_examples):
            print(f"- {ex}")

    print(f"Failed jobs: {failed}")
    raise SystemExit(1 if failed else 0)

