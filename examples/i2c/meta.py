# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os, sys
import argparse
from typing import List
from dataclasses import dataclass
from acacia import System, ProtectionDomain, MemoryRegion, Channel, DeviceTreeBlob, Map

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../"))
from acacia_sddf import BOARDS, sDDFI2C, sDDFSerial, sDDFTimer


def generate(sdf_file: str, output_dir: str, dtb: DeviceTreeBlob):
    client_pn532 = ProtectionDomain("client_pn532", "client_pn532.elf", sdf, priority=1)
    client_ds3231 = ProtectionDomain("client_ds3231", "client_ds3231.elf", sdf, priority=1)

    i2c = sDDFI2C(
        board.i2c.compatible, board.i2c.node_path, sdf, driver_prio=200, virt_prio=199
    )
    i2c.add_client(client_ds3231)
    i2c.add_client(client_pn532)

    timer = sDDFTimer(board.timer.compatible, board.timer.node_path, sdf)
    timer.add_client(client_ds3231)
    timer.add_client(client_pn532)

    serial = sDDFSerial(
        board.serial.compatible,
        board.serial.node_path,
        sdf,
        driver_prio=201,
        virt_tx_prio=200,
        allow_rx=False,
        enable_color=False,
        baud_rate=board.baud_rate if board.baud_rate else 115200,
    )
    serial.add_client(client_ds3231)
    serial.add_client(client_pn532)

    if board.name == "odroidc4":
        # Odroid-C4 I2C requires clocks/GPIO setup, for now we give the I2C driver
        # direct access.
        clk_mr = MemoryRegion("clk", 0x1000, sdf, paddr=0xFF63C000, cached=False)
        gpio_mr = MemoryRegion("gpio", 0x1000, sdf, paddr=0xFF634000, cached=False)
        i2c.driver.add_map(Map(clk_mr, 0x30_000_000, "rw"))
        i2c.driver.add_map(Map(gpio_mr, 0x30_100_000, "rw"))

    out_file = f"{output_dir}/{sdf_file}"
    sdf.make_config_structs()
    print(f"Saving to {out_file}")
    sdf.write_xml_file(out_file)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    dtb = DeviceTreeBlob(args.dtb)
    sdf = System(board.arch, board.paddr_top, dtb)

    generate(args.sdf, args.output, dtb)
