#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from asyncio.subprocess import STDOUT, PIPE

from .base import HardwareBackend


class QemuBackend(HardwareBackend):
    def __init__(self, invocation_exe: str, *invocation_args: str):
        self.process = None
        self.invocation_exe = invocation_exe
        self.invocation_args = list(invocation_args)

    async def start(self):
        assert self.process is None, "start() not previously called"
        self.process = await asyncio.create_subprocess_exec(
            self.invocation_exe,
            *self.invocation_args,
            stdin=PIPE,
            stdout=PIPE,
            stderr=STDOUT,
        )

    async def stop(self):
        assert self.process is not None, "process not running"
        try:
            self.process.terminate()
            await self.process.wait()
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
