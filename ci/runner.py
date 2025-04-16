#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

"""
Runner (CLI) script for running the hardware tests automagically.
This includes automatic, interactive tests using our "Machine Queue" or within
QEMU.
"""

import asyncio
from pathlib import Path
import sys

from .hardware_backend import (
    HardwareBackend,
    MachineQueueBackend,
    QemuBackend,
    TtyBackend,
)


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


# TODO: Figure out how to get this to work with unittest so we have autodiscovery
#       and listing.
# TODO: Figure out how to structure this in a good way. cc @Ivan.
def cli(test):
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--file",
        type=Path,
        required=True,
    )
    parser.add_argument(
        "--backend",
        choices=["qemu", "machine_queue", "tty"],
        required=True,
    )
    parser.add_argument(
        "--board",
        choices=["odroidc4_1", "qemu_virt_riscv64"],
        required=True,
    )
    args = parser.parse_args()

    if args.backend == "qemu":
        backend = QemuBackend("make", "MICROKIT_BOARD=qemu_virt_riscv64", "qemu", "-C", "examples/serial")
    elif args.backend == "machine_queue":
        backend = MachineQueueBackend(args.file, "odroidc4_1")
    elif args.backend == "tty":
        backend = TtyBackend("/dev/ttyUSB0")
    else:
        raise Exception("Unknown backend %s" % (args.backend))

    asyncio.run(runner(test, backend))


if __name__ == "__main__":
    # TODO:
    ...


# python -m ci.tests.examples.serial --backend machine_queue --file examples/serial/build/loader.img
# python -m ci.tests.examples.serial --backend qemu --board qemu_virt_riscv64 --file examples/serial/build/loader.img
# python -m ci.tests.examples.serial --backend machine_queue --board odroidc4_1 --file examples/serial/build/loader.img
