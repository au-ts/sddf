# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

"""
Multi-kernel Convenience script to build Microkit SDK and images for each kernel.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from acacia import LargePage

def run(command, **kwargs):
    subprocess.run([str(arg) for arg in command], check=True, **kwargs)

def build_sdk(args, kernel, sdk, start_harts):
    env = {k: v for k, v in os.environ.items() if k not in ("MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES")}
    run([sys.executable, args.microkit.resolve() / "build_sdk.py",
         "--sel4", args.sel4.resolve(),
         "--boards", args.board,
         "--configs", args.config,
         "--dts", args.dts.resolve(),
         "--dts-overlay", args.directory / f"{kernel['name']}.overlay.dts",
         "--loader-address", hex(kernel["loader_address"]),
         *start_harts,
         "--sdk-dir", sdk,
         "--build-dir", sdk.parent / "build",
         "--gcc-toolchain-prefix-riscv64", args.cross_compiler_prefix.rstrip("-"),
         "--skip-tool", "--skip-docs", "--skip-tar",
         *(["--llvm"] if args.llvm else [])],
        cwd=args.microkit.resolve(), env=env)

def build(args):
    args.directory = args.directory.resolve()
    microkit_tool = (Path(os.environ["MICROKIT_SDK"]) / "bin" / "microkit").resolve()
    kernels = json.loads((args.directory / "kernels.json").read_text())
    starts = [arg for kernel in kernels[1:]
            for arg in ("--start-hart", kernel["hart"], hex(kernel["loader_address"]))]

    for index,kernel in enumerate(kernels):
        name = kernel["name"]
        sdk = args.directory / name / "sdk"
        build_sdk(args, kernel, sdk, starts if index == 0 else [])
        image = args.directory / f"{name}.elf"
        run([microkit_tool,
             args.directory / f"{name}.system",
             "--board", args.board,
             "--config", args.config,
             "--search-path", args.directory.parent,
             "--image-type", "elf",
             "-o", image,
             "-r", args.directory / f"{name}-report.txt"],
            cwd=args.directory, env=dict(os.environ, MICROKIT_SDK=str(sdk)))

        if kernel["loader_address"] + image.stat().st_size > kernel["ram"][1]:
            raise ValueError(f"{image} exceeds its private RAM. Increase the kernel partitions private RAM")
        print(f"{name}: {image} (hart {kernel['hart']})")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True, help="Acacia's multikernel output directory")
    parser.add_argument("--dts", type=Path, required=True, help="The hardware DTS used by the meta program")
    parser.add_argument("--sel4", type=Path, required=True)
    parser.add_argument("--microkit", type=Path, required=True, help="Microkit source directory")
    parser.add_argument("--board", required=True)
    parser.add_argument("--config", default="debug")
    parser.add_argument("--cross-compiler-prefix", default="riscv64-unknown-elf-")
    parser.add_argument("--llvm", action="store_true")
    build(parser.parse_args())
