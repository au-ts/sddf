#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import os
from signal import SIGHUP, SIGINT
import asyncio
from asyncio.subprocess import PIPE, STDOUT
from pathlib import Path

from .. import log
from .base import HardwareBackend
from .common import LockedBoardException, TestFailureException, TestRetryException
from .streams import wait_for_output

# In case we somehow break and don't release the lock automatically.
# TODO: inherit from somewhere else
LOCK_TIMEOUT = 120 * 60  # 120 minutes
START_TIMEOUT = 60  # 1 minute
# For Github Actions etc.
IS_CI = bool(os.environ.get("CI"))


def flatten(xss):
    return [x for xs in xss for x in xs]


class IpBenchQueueBackend(HardwareBackend):
    def __init__(
        self,
        clients: list[str],
        benchmark_script: Path,
        target_ip: str,
        throughputs: list[int],
        samples: int,
    ):
        """
        clients is the list of valid bench clients used with iq.sh
        """
        self.clients = clients
        self.target_ip = target_ip
        self.benchmark_script = benchmark_script
        self.throughputs = throughputs
        self.samples = samples
        self.process = None

        if IS_CI:
            self.job_key = "-".join(
                [
                    "au_ts_ci",
                    os.environ.get("GITHUB_REPOSITORY", "??"),
                    os.environ.get("GITHUB_WORKFLOW", "??"),
                    os.environ.get("GITHUB_RUN_ID", "??"),
                    os.environ.get("GITHUB_JOB", "??"),
                    os.environ.get("INPUT_INDEX", "$0")[1:],
                ]
            )
        else:
            self.job_key = "au_ts_ci (running locally)"

    async def start(self):
        assert self.process is None, "start() should only be called once"

        self.process = await asyncio.create_subprocess_exec(
            # fmt: off
            "iq.sh", "run",
            "-k", self.job_key,
            "-T", str(LOCK_TIMEOUT),
            # only try to acquire once
            "-t", "0",
            "-f", self.benchmark_script.resolve(),
            *flatten(("-c", client) for client in self.clients),
            "--",
            self.target_ip,
            "--throughputs", *[str(t) for t in self.throughputs],
            "--samples", str(self.samples),
            "--clients", *[c for c in self.clients],
            # fmt: on
            stdin=PIPE,
            stdout=PIPE,
            stderr=STDOUT,
        )

        try:
            async with asyncio.timeout(START_TIMEOUT):
                await wait_for_output(self, b"[IpbenchTestTarget:__init__] : client " + self.target_ip.encode() + b"\n")
        except asyncio.IncompleteReadError as e:
            if (b"Failed to acquire lock for" in e.partial) \
                or (b"Attempting to grab lock you already own" in e.partial) \
                or (b"Giving up; releasing newly locked systems" in e.partial):
                raise TestRetryException() from e

            raise

    async def stop(self):
        if self.process is None:
            return

        # XXX: I think this doesn't work.

        try:
            # Use SIGHUP to close the console (releases lock implicitly)
            self.process.send_signal(SIGINT)
            # Use transport.close() because await process.wait() deadlocks
            self.process._transport.close()  # type: ignore
        except ProcessLookupError:
            pass

    @property
    def input_stream(self) -> asyncio.StreamWriter:
        assert self.process is not None, "process not running"
        return self.process.stdin  # type: ignore

    @property
    def output_stream(self) -> asyncio.StreamReader:
        assert self.process is not None, "process not running"
        return self.process.stdout  # type: ignore
