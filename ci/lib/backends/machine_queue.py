#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import os
from signal import SIGHUP
import asyncio
from asyncio.subprocess import PIPE, STDOUT
from pathlib import Path
import sys

from .base import HardwareBackend
from .common import LockedBoardException

# In case we somehow break and don't release the lock automatically.
LOCK_TIMEOUT = 60 * 60  # 60 min
# For Github Actions etc.
IS_CI = bool(os.environ.get("CI"))


class MachineQueueBackend(HardwareBackend):
    def __init__(self, image_file: Path, boards: list[str]):
        """
        board should be given with underscores, e.g. odroidc4_1
        """
        self.image_file = image_file
        self.boards = boards
        self.chosen_board = None
        self.process = None

        if IS_CI:
            self.job_key = "-".join(
                [
                    os.environ.get("GITHUB_REPOSITORY", "hardware_ci"),
                    os.environ.get("GITHUB_WORKFLOW", "??"),
                    os.environ.get("GITHUB_RUN_ID", "??"),
                    os.environ.get("GITHUB_JOB", "??"),
                    os.environ.get("INPUT_INDEX", "$0")[1:],
                ]
            )
        else:
            self.job_key = "hardware_ci (testing at the moment, take the lock if @juliab holds this)"

    @staticmethod
    async def _lock_info(board: str):
        # Print out the lock info.
        lock_info = await asyncio.create_subprocess_exec(
            # fmt: off
            "mq.sh", "sem", "-mr-info", board,
            # fmt: on
            stdout=PIPE,
            stderr=None,  # inherit -> print
        )

        stdout, _ = await lock_info.communicate()
        assert (
            b"LOCKED" in stdout or b"FREE" in stdout
        ), f"one of locked or free ({stdout})"

        return stdout.decode().strip("\n")

    async def _find_available_board(self) -> str:
        lock_infos = []
        for board in self.boards:
            lock_info = await self._lock_info(board)
            if "FREE" in lock_info:
                return board

            lock_infos.append(lock_info)

        raise LockedBoardException("\n".join(lock_infos))

    async def _acquire_lock(self):
        assert self.chosen_board is not None

        get_lock = await asyncio.create_subprocess_exec(
            # fmt: off
            "mq.sh", "sem",
            "-wait", self.chosen_board,
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
            # Race condition, someone acquired the lock between our search and now.
            # This should be rare, so let's just handle this with lock retries later.
            lock_info = await self._lock_info(self.chosen_board)
            raise LockedBoardException(lock_info)

        assert return_code == 0, "board should have locked successfully; unknown error."

        lock_info = await self._lock_info(self.chosen_board)
        print("Acquired lock:", lock_info, file=sys.stderr)

    async def _release_lock(self):
        assert self.chosen_board is not None

        lock_info = await self._lock_info(self.chosen_board)
        # someone else might have grabbed and affected our tests... not great.
        assert "LOCKED" in lock_info, "somehow we don't have a lock - did we timeout?"

        release_lock = await asyncio.create_subprocess_exec(
            # fmt: off
            "mq.sh", "sem",
            "-signal", self.chosen_board,
            "-k", self.job_key,
            # fmt: on
            stdout=None,  # inherit -> print
            stderr=None,  # inherit -> print
        )

        return_code = await release_lock.wait()
        assert return_code == 0, "couldn't unlock board for unknown reason"

        lock_info = await self._lock_info(self.chosen_board)
        print("Released lock:", lock_info, file=sys.stderr)

    async def start(self):
        assert self.process is None, "start() should only be called once"

        self.chosen_board = await self._find_available_board()
        await self._acquire_lock()

        self.process = await asyncio.create_subprocess_exec(
            # fmt: off
            "mq.sh", "run",
            "-n",  # don't touch the lock, we already have it.
            "-c", "",  # no completion text, so we get stdin as soon as possible
            "-a",  # keep the board running after "completion" text
            "-f", self.image_file.resolve(),
            "-s", self.chosen_board,
            # fmt: on
            stdin=PIPE,
            stdout=PIPE,
            stderr=STDOUT,
        )

    async def stop(self):
        assert self.process is not None

        await self._release_lock()

        try:
            # Use SIGHUP to close the console
            self.process.send_signal(SIGHUP)
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
