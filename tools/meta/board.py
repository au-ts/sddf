# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
from dataclasses import dataclass
from typing import List, Tuple, Optional
from sdfgen import SystemDescription


@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    serial: Optional[str] = None
    ethernet: Optional[str] = None
    timer: Optional[str] = None
    i2c: Optional[str] = None
    partition: int = 0
    blk: Optional[str] = None


# Keep this list in alphabetical order by board name
# TODO: convert to Dictionary
BOARDS: List[Board] = [
    Board(
        name="cheshire",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0x90000000,
        serial="soc/serial@3002000",
        i2c="soc/i2c@3003000",
    ),
    Board(
        name="hifive_p550",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0xA0000000,
        serial="soc/serial@0x50900000",
    ),
    Board(
        name="imx8mm_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/spba-bus@30800000/serial@30890000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet="soc@0/bus@30800000/ethernet@30be0000",
    ),
    Board(
        name="imx8mp_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/spba-bus@30800000/serial@30890000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet="soc@0/bus@30800000/ethernet@30bf0000",
    ),
    Board(
        name="imx8mp_iotgate",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/serial@30890000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet="soc@0/bus@30800000/ethernet@30bf0000",
    ),
    Board(
        name="imx8mq_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/serial@30860000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet="soc@0/bus@30800000/ethernet@30be0000",
    ),
    Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/serial@30860000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet="soc@0/bus@30800000/ethernet@30be0000",
        blk="soc@0/bus@30800000/mmc@30b40000",
        partition=2,
    ),
    Board(
        name="odroidc2",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x60000000,
        serial="soc/bus@c8100000/serial@4c0",
        timer="soc/bus@c1100000/watchdog@98d0",
        ethernet="soc/ethernet@c9410000",
    ),
    Board(
        name="odroidc4",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x60000000,
        i2c="soc/bus@ffd00000/i2c@1d000",
        serial="soc/bus@ff800000/serial@3000",
        timer="soc/bus@ffd00000/watchdog@f0d0",
        ethernet="soc/ethernet@ff3f0000",
    ),
    Board(
        name="qemu_virt_aarch64",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x6_0000_000,
        serial="pl011@9000000",
        timer="timer",
        blk="virtio_mmio@a003e00",
        ethernet="virtio_mmio@a003e00",
        i2c=None,
    ),
    Board(
        name="qemu_virt_riscv64",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0xA_0000_000,
        serial="soc/serial@10000000",
        timer="soc/rtc@101000",
        ethernet="soc/virtio_mmio@10008000",
        blk="soc/virtio_mmio@10008000",
        partition=0,
        i2c=None,
    ),
    Board(
        name="rpi4b_1gb",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x2_000_000,
        serial="soc/serial@7e215040",
        timer="soc/timer@7e003000",
    ),
    Board(
        name="serengeti",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0x90000000,
        serial="soc/serial@3002000",
        timer="soc/timer@300B000",
        i2c="soc/i2c@3003000",
    ),
    Board(
        name="star64",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0x100000000,
        serial="soc/serial@10000000",
        timer="soc/timer@13050000",
        ethernet="soc/ethernet@16030000",
    ),
    Board(
        name="zcu102",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA0000000,
        timer="axi/timer@ff140000",
        serial="axi/serial@ff000000",
        ethernet="axi/ethernet@ff0e0000",
    ),
    Board(
        name="x86_64_generic",
        arch=SystemDescription.Arch.X86_64,
        paddr_top=0x7FFDF000,
        timer=None,
        serial=None,
    ),
]
