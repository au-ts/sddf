#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from abc import ABC, abstractmethod
from asyncio import StreamReader, StreamWriter


class HardwareBackend(ABC):
    @abstractmethod
    async def start(self):
        """Start the hardware and wait for it to have booted"""

    @abstractmethod
    async def stop(self):
        """Stop the hardware"""

    @property
    @abstractmethod
    def output_stream(self) -> StreamReader: ...

    @property
    @abstractmethod
    def input_stream(self) -> StreamWriter: ...
