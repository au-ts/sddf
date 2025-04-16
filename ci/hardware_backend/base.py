#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from abc import ABC, abstractmethod
from asyncio import StreamReader, StreamWriter


class HardwareBackend(ABC):
    @abstractmethod
    async def start(self): ...

    @abstractmethod
    async def stop(self): ...

    @property
    @abstractmethod
    def output_stream(self) -> StreamReader: ...

    @property
    @abstractmethod
    def input_stream(self) -> StreamWriter: ...


class LockedBoardException(Exception):
    """Board is locked and we were told not to poll."""
