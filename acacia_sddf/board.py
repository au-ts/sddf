# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
from dataclasses import dataclass
from typing import List, Optional, Tuple
from acacia import System, ProtectionDomain, aarch64, riscv64, x86_64, Arch
from importlib.metadata import version


@dataclass(frozen=True)
class DriverDouble:
    compatible: str
    node_path: str


@dataclass
class Board:
    name: str
    arch: Arch
    paddr_top: int
    # Driver mappings -> (compatible, preferred_node) tuples
    serial: Optional[DriverDouble] = DriverDouble(None, None)
    ethernet: Optional[DriverDouble] = DriverDouble(None, None)
    timer: Optional[DriverDouble] = DriverDouble(None, None)
    i2c: Optional[DriverDouble] = DriverDouble(None, None)
    blk: Optional[DriverDouble] = DriverDouble(None, None)
    partition: int = 0
    baud_rate: Optional[int] = None


# Keep this list in alphabetical order by board name
# TODO: convert to Dictionary
BOARDS: List[Board] = [
    Board(
        name="cheshire",
        arch=riscv64,
        paddr_top=0x90000000,
    ),
    Board(
        name="hifive_p550",
        arch=riscv64,
        paddr_top=0xA0000000,
    ),
    Board(
        name="imx8mm_evk",
        arch=aarch64,
        paddr_top=0x70000000,
        timer=DriverDouble("fsl,imx8mm-gpt", "soc@0/bus@30000000/timer@302d0000"),
    ),
    Board(
        name="imx8mp_evk",
        arch=aarch64,
        paddr_top=0x70000000,
        timer=DriverDouble("fsl,imx8mp-gpt", "soc@0/bus@30000000/timer@302d0000"),
    ),
    Board(
        name="imx8mp_iotgate",
        arch=aarch64,
        paddr_top=0x70000000,
        timer=DriverDouble("fsl,imx8mp-gpt", "soc@0/bus@30000000/timer@302d0000"),
    ),
    Board(
        name="imx8mq_evk",
        arch=aarch64,
        paddr_top=0x70000000,
        timer=DriverDouble("fsl,imx8mq-gpt", "soc@0/bus@30000000/timer@302d0000"),
    ),
    Board(
        name="kria_k26",
        arch=aarch64,
        paddr_top=0x70000000,
        timer=DriverDouble("cdns,ttc", "axi/timer@ff140000"),
    ),
    Board(
        name="maaxboard",
        arch=aarch64,
        paddr_top=0x70000000,
        timer=DriverDouble("fsl,imx8mq-gpt", "soc@0/bus@30000000/timer@302d0000"),
        partition=2,
    ),
    Board(
        name="odroidc2",
        arch=aarch64,
        paddr_top=0x60000000,
        timer=DriverDouble("amlogic,meson-gxbb-wdt", "soc/bus@c1100000/watchdog@98d0"),
        baud_rate=115200,
    ),
    Board(
        name="odroidc4",
        arch=aarch64,
        paddr_top=0x60000000,
        timer=DriverDouble("amlogic,meson-gxbb-wdt", "soc/bus@ffd00000/watchdog@f0d0"),
        baud_rate=115200,
    ),
    Board(
        name="qemu_virt_aarch64",
        arch=aarch64,
        paddr_top=0x6_0000_000,
        timer=DriverDouble("arm,armv8-timer", "timer"),
    ),
    Board(
        name="qemu_virt_riscv64",
        arch=riscv64,
        paddr_top=0xA_0000_000,
        timer=DriverDouble("google,goldfish-rtc", "soc/rtc@101000"),
        partition=0,
    ),
    Board(
        name="rock3b",
        arch=aarch64,
        paddr_top=0xEC000000,
        timer=DriverDouble("rockchip,rk3568-timer", "rktimer@fe5f0000"),
        baud_rate=1500000,
    ),
    Board(
        name="rpi4b_1gb",
        arch=aarch64,
        paddr_top=0x2_000_000,
        timer=DriverDouble("brcm,bcm2835-system-timer", "soc/timer@7e003000"),
    ),
    Board(
        name="serengeti",
        arch=riscv64,
        paddr_top=0x90000000,
        timer=DriverDouble("pulp,apb_timer", "soc/timer@300B000"),
    ),
    Board(
        name="star64",
        arch=riscv64,
        paddr_top=0x100000000,
        timer=DriverDouble("starfive,jh7110-timer", "soc/timer@13050000"),
    ),
    Board(
        name="zcu102",
        arch=aarch64,
        paddr_top=0x80000000,
        timer=DriverDouble("cdns,ttc", "axi/timer@ff140000"),
    ),
    Board(
        name="x86_64_generic",
        arch=x86_64,
        paddr_top=0x7FFDF000,
    ),
    Board(
        name="x86_64_generic_vtx",
        arch=x86_64,
        paddr_top=0x7FFDF000,
    ),
]
