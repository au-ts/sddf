#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

"""Polyfills for older python versions"""

import asyncio
import contextlib
import enum
import os
from types import TracebackType
from typing import Optional, Type

# Python 3.11
if not hasattr(contextlib, "chdir"):

    @contextlib.contextmanager
    def chdir(path):
        old_cwd = os.getcwd()
        os.chdir(path)
        try:
            yield
        finally:
            os.chdir(old_cwd)

    contextlib.chdir = chdir


# Python 3.11
if not hasattr(asyncio, "timeout"):

    class _State(enum.Enum):
        INIT = "INIT"
        ENTER = "ENTER"
        TIMEOUT = "TIMEOUT"
        EXIT = "EXIT"

    class Timeout:
        # From https://github.com/aio-libs/async-timeout/blob/master/async_timeout/__init__.py#L135-L276
        def __init__(
            self, deadline: Optional[float], loop: asyncio.AbstractEventLoop
        ) -> None:
            self._loop = loop
            self._state = _State.INIT

            self._task: Optional["asyncio.Task[object]"] = None
            self._timeout_handler = None  # type: Optional[asyncio.Handle]
            self._deadline = deadline

        async def __aenter__(self) -> "Timeout":
            self._do_enter()
            return self

        async def __aexit__(
            self,
            exc_type: Optional[Type[BaseException]],
            exc_val: Optional[BaseException],
            exc_tb: Optional[TracebackType],
        ) -> Optional[bool]:
            self._do_exit(exc_type)
            return None

        def _reject(self) -> None:
            self._task = None
            if self._timeout_handler is not None:
                self._timeout_handler.cancel()
                self._timeout_handler = None

        def _reschedule(self) -> None:
            assert self._state == _State.ENTER
            deadline = self._deadline
            if deadline is None:
                return

            now = self._loop.time()
            if self._timeout_handler is not None:
                self._timeout_handler.cancel()

            self._task = asyncio.current_task()
            if deadline <= now:
                self._timeout_handler = self._loop.call_soon(self._on_timeout)
            else:
                self._timeout_handler = self._loop.call_at(deadline, self._on_timeout)

        def _do_enter(self) -> None:
            if self._state != _State.INIT:
                raise RuntimeError(f"invalid state {self._state.value}")
            self._state = _State.ENTER
            self._reschedule()

        def _do_exit(self, exc_type: Optional[Type[BaseException]]) -> None:
            if exc_type is asyncio.CancelledError and self._state == _State.TIMEOUT:
                assert self._task is not None
                self._timeout_handler = None
                self._task = None
                raise asyncio.TimeoutError
            # timeout has not expired
            self._state = _State.EXIT
            self._reject()
            return None

        def _on_timeout(self) -> None:
            assert self._task is not None
            self._task.cancel()
            self._state = _State.TIMEOUT
            # drop the reference early
            self._timeout_handler = None

    def timeout(delay: Optional[float]) -> Timeout:
        loop = asyncio.get_running_loop()
        return Timeout(loop.time() + delay if delay is not None else None, loop)

    asyncio.timeout = timeout
