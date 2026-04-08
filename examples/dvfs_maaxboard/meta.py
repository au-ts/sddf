# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os, sys
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)
from board import BOARDS

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    # Increase the stack size as running with UBSAN uses more stack space than normal.
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx", "serial_virt_tx.elf", priority=199, stack_size=0x2000
    )

    # timer driver should be highest prio for sanity
    # i2c must be higher priority than pmic
    # pmic must be higher priority than dvfs
    # clk must be higher prio than dvfs
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=200)
    clk_driver = ProtectionDomain("clk_driver", "clk_driver.elf", priority=110, passive=True)
    i2c_driver = ProtectionDomain("i2c_driver", "i2c_driver.elf", priority=102)
    i2c_virt = ProtectionDomain("i2c_virt", "i2c_virt.elf", priority=101)
    pmic_driver = ProtectionDomain("pmic_driver", "pmic_driver.elf", priority=100)
    dvfs_driver = ProtectionDomain("dvfs_driver", "dvfs_driver.elf", priority=99, passive=True)
    client = ProtectionDomain("client", "client.elf", priority=1)

    timer_node = dtb.node(board.timer)
    assert timer_node is not None
    serial_node = dtb.node(board.serial)
    assert serial_node is not None
    i2c_node = dtb.node(board.i2c)
    assert i2c_node is not None

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)
    serial_system = Sddf.Serial(
        sdf, serial_node, serial_driver, serial_virt_tx, enable_color=False
    )
    serial_system.add_client(client)

    i2c_system = Sddf.I2c(sdf, i2c_node, i2c_driver, i2c_virt)
    i2c_system.add_client(pmic_driver)

    # HACK: sdfgen doesn't support multiple regions for a device resource yet
    #       or the clk class. This will be removed in the pending sdfgen refactor.
    #       We can add direct support for the Maaxboard via boards.py, but
    #       the odroid clk driver depends on numerous maps that aren't in the DTS
    #       at all, meaning this switch is the best we can do for now.
    regions = []    # tuples of (mr, map var name)
    if board.name == "maaxboard":
        clk_ccm_mr = MemoryRegion(sdf, "clk_ccm", 0xd000, paddr=0x30380000)
        clk_ccm_analog_mr = MemoryRegion(sdf, "clk_ccm_analog", 0x1000, paddr=0x30360000)
        sdf.add_mr(clk_ccm_mr)
        sdf.add_mr(clk_ccm_analog_mr)

        clk_ccm_map = Map(clk_ccm_mr, 0x3200000, "rw", cached=False)
        clk_ccm_analog_map = Map(clk_ccm_analog_mr, 0x3300000, "rw", cached=False)
        clk_driver.add_map(clk_ccm_map)
        clk_driver.add_map(clk_ccm_analog_map)
    else:
        print("Unsupported board!")
        exit(-1)


    # add channels
    # TODO: replace with sdfgen invocations
    clk_channel = Channel(clk_driver, dvfs_driver, pp_b=True)
    sdf.add_channel(clk_channel)

    pmic_channel = Channel(pmic_driver, dvfs_driver, pp_b=True)
    sdf.add_channel(pmic_channel)

    dvfs_channel = Channel(dvfs_driver, client, pp_b=True)
    sdf.add_channel(dvfs_channel)

    pds = [
        dvfs_driver,
        clk_driver,
        serial_driver,
        serial_virt_tx,
        timer_driver,
        pmic_driver,
        i2c_driver,
        i2c_virt,
        client,
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert i2c_system.connect()
    assert i2c_system.serialise_config(output_dir)
    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)
