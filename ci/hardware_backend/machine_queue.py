#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from signal import SIGHUP
import asyncio
from asyncio.subprocess import PIPE, STDOUT
from pathlib import Path
import sys

from .base import HardwareBackend, LockedBoardException

# In case we somehow break and don't release the lock automatically.
LOCK_TIMEOUT = 60 * 60  # 60 min


class MachineQueueBackend(HardwareBackend):
    def __init__(self, image_file: Path, board: str, poll_lock=False):
        """
        board should be given with underscores, e.g. odroidc4_1
        """
        self.image_file = image_file
        self.board = board
        self.poll_lock = poll_lock
        self.job_key = "julia: feel free to release this lock"

        self.process = None

    async def _lock_info(self):
        # Print out the lock info.
        lock_info = await asyncio.create_subprocess_exec(
            # fmt: off
            "mq.sh", "sem", "-mr-info", self.board,
            # fmt: on
            stdout=PIPE,
            stderr=None,  # inherit -> print
        )

        stdout, _ = await lock_info.communicate()
        assert b"LOCKED" in stdout or b"FREE" in stdout, f"one of locked or free ({stdout})"

        return stdout

    async def start(self):
        assert self.process is None, "start() should only be called once"

        lock_info = await self._lock_info()
        if b"LOCKED" in lock_info and not self.poll_lock:
            raise LockedBoardException(lock_info.decode().strip())

        get_lock = await asyncio.create_subprocess_exec(
            # fmt: off
            "mq.sh", "sem",
            "-wait", self.board,
            "-k", self.job_key,
            "-T", str(LOCK_TIMEOUT),
            "-t", "0",
            # only try to acquire once.
            # fmt: on
            stdout=None,  # inherit -> print
            stderr=None,  # inherit -> print
        )
        return_code = await get_lock.wait()
        if return_code == 2:
            # Race condition, someone acquired the lock between our check and now.
            # TODO: print who?
            raise LockedBoardException()

        assert return_code == 0, "couldn't lock board for unknown error"

        lock_info = await self._lock_info()
        print("Acquired lock:", lock_info.decode().strip("\n"), file=sys.stderr)

        self.process = await asyncio.create_subprocess_exec(
            # fmt: off
            "mq.sh", "run",
            "-n",  # don't touch the lock, we already have it.
            "-c", "",  # no completion text, so we get stdin as soon as possible
            "-a",  # keep the board running after "completion" text
            "-f", self.image_file.resolve(),
            "-s", self.board,
            # fmt: on
            stdin=PIPE,
            stdout=PIPE,
            stderr=STDOUT,
        )

    async def stop(self):
        lock_info = await self._lock_info()
        # someone else might have grabbed and affected our tests... not great.
        assert b"LOCKED" in lock_info, "somehow we don't have a lock - did we timeout?"

        release_lock = await asyncio.create_subprocess_exec(
            # fmt: off
            "mq.sh", "sem",
            "-signal", self.board,
            "-k", self.job_key,
            # fmt: on
            stdout=None,  # inherit -> print
            stderr=None,  # inherit -> print
        )
        return_code = await release_lock.wait()
        assert return_code == 0, "couldn't unlock board for unknown error"

        lock_info = await self._lock_info()
        print("Released lock:", lock_info.decode().strip("\n"), file=sys.stderr)

        try:
            # Use SIGHUP to close the console
            self.process.send_signal(SIGHUP)
            # Use transport.close() because await process.wait() deadlocks
            self.process._transport.close()
        except ProcessLookupError:
            pass

    @property
    def input_stream(self):
        assert self.process is not None, "process not running"
        return self.process.stdin

    @property
    def output_stream(self):
        assert self.process is not None, "process not running"
        return self.process.stdout
