#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from .base import HardwareBackend


class TtyBackend(HardwareBackend):
    def __init__(self, path: str, baudrate=115200):
        self.path = path
        self.baudrate = baudrate

        self.reader = None
        self.writer = None

        try:
            import serial_asyncio_fast
        except ImportError:
            raise ModuleNotFoundError(
                "no module 'serial_asyncio_fast; install 'pyserial-asyncio-fast'"
            )

    async def start(self):
        assert self.reader is None, "start() not previously called"

        self.reader, self.writer = await serial_asyncio_fast.open_serial_connection(
            url=self.path,
            baudrate=self.baudrate,
        )

    async def stop(self):
        assert self.reader is not None, "tty not connected"
        self.writer.close()

    @property
    def input_stream(self):
        assert self.writer is not None, "tty not connected"
        return self.writer

    @property
    def output_stream(self):
        assert self.reader is not None, "tty not connect"
        return self.reader
