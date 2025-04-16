#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

"""
Runner (CLI) script for running the hardware tests automagically.
This includes automatic, interactive tests using our "Machine Queue" or within
QEMU.
"""

import asyncio
import sys

from ci.hardware_backend import HardwareBackend


async def runner(test, backend: HardwareBackend):
    await backend.start()
    try:
        await test(backend)
    except asyncio.CancelledError:
        # Reset coloured output.
        print("\x1b[0m\n")
        print("Task cancelled, exiting...", file=sys.stderr)
    except EOFError:
        print("\x1b[0m")
        print("Error: EOF when reading from backend stream", file=sys.stderr)
        quit(1)
    finally:
        await backend.stop()
