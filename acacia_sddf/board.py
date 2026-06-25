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
        serial=DriverDouble("ns16550a", "soc/serial@3002000"),
        i2c=DriverDouble("eth,i2c", "soc/i2c@3003000"),
    ),
    Board(
        name="hifive_p550",
        arch=riscv64,
        paddr_top=0xA0000000,
        serial=DriverDouble("snps,dw-apb-uart", "soc/serial@0x50900000"),
    ),
    Board(
        name="imx8mm_evk",
        arch=aarch64,
        paddr_top=0x70000000,
        serial=DriverDouble("fsl,imx8mm-uart", "soc@0/bus@30800000/spba-bus@30800000/serial@30890000"),
        timer=DriverDouble("fsl,imx8mm-gpt", "soc@0/bus@30000000/timer@302d0000"),
        ethernet=DriverDouble("", "soc@0/bus@30800000/ethernet@30be0000"),
    ),
    Board(
        name="imx8mp_evk",
        arch=aarch64,
        paddr_top=0x70000000,
        serial=DriverDouble("fsl,imx8mp-uart", "soc@0/bus@30800000/spba-bus@30800000/serial@30890000"),
        timer=DriverDouble("fsl,imx8mp-gpt", "soc@0/bus@30000000/timer@302d0000"),
        ethernet=DriverDouble("", "soc@0/bus@30800000/ethernet@30bf0000"),
    ),
    Board(
        name="imx8mp_iotgate",
        arch=aarch64,
        paddr_top=0x70000000,
        serial=DriverDouble("fsl,imx8mp-uart", "soc@0/bus@30800000/serial@30890000"),
        timer=DriverDouble("fsl,imx8mp-gpt", "soc@0/bus@30000000/timer@302d0000"),
        ethernet=DriverDouble("", "soc@0/bus@30800000/ethernet@30bf0000"),
    ),
    Board(
        name="imx8mq_evk",
        arch=aarch64,
        paddr_top=0x70000000,
        serial=DriverDouble("fsl,imx8mq-uart", "soc@0/bus@30800000/serial@30860000"),
        timer=DriverDouble("fsl,imx8mq-gpt", "soc@0/bus@30000000/timer@302d0000"),
        ethernet=DriverDouble("", "soc@0/bus@30800000/ethernet@30be0000"),
    ),
    Board(
        name="kria_k26",
        arch=aarch64,
        paddr_top=0x70000000,
        timer=DriverDouble("cdns,ttc", "axi/timer@ff140000"),
        serial=DriverDouble("xlnx,zynqmp-uart", "axi/serial@ff010000"),
    ),
    Board(
        name="maaxboard",
        arch=aarch64,
        paddr_top=0x70000000,
        serial=DriverDouble("fsl,imx8mq-uart", "soc@0/bus@30800000/serial@30860000"),
        timer=DriverDouble("fsl,imx8mq-gpt", "soc@0/bus@30000000/timer@302d0000"),
        ethernet=DriverDouble("", "soc@0/bus@30800000/ethernet@30be0000"),
        blk=DriverDouble("", "soc@0/bus@30800000/mmc@30b40000"),
        partition=2,
    ),
    Board(
        name="odroidc2",
        arch=aarch64,
        paddr_top=0x60000000,
        serial=DriverDouble("amlogic,meson-gx-uart", "soc/bus@c8100000/serial@4c0"),
        timer=DriverDouble("amlogic,meson-gxbb-wdt", "soc/bus@c1100000/watchdog@98d0"),
        ethernet=DriverDouble("", "soc/ethernet@c9410000"),
        baud_rate=115200
    ),
    Board(
        name="odroidc4",
        arch=aarch64,
        paddr_top=0x60000000,
        i2c=DriverDouble("amlogic,meson-axg-i2c", "soc/bus@ffd00000/i2c@1d000"),
        serial=DriverDouble("amlogic,meson-gx-uart", "soc/bus@ff800000/serial@3000"),
        timer=DriverDouble("amlogic,meson-gxbb-wdt", "soc/bus@ffd00000/watchdog@f0d0"),
        ethernet=DriverDouble("amlogic,meson-gx-uart", "soc/ethernet@ff3f0000"),
        baud_rate=115200
    ),
    Board(
        name="qemu_virt_aarch64",
        arch=aarch64,
        paddr_top=0x6_0000_000,
        serial=DriverDouble("arm,pl011", "pl011@9000000"),
        timer=DriverDouble("arm,armv8-timer", "timer"),
        blk=DriverDouble("", "virtio_mmio@a000200"),
        ethernet=DriverDouble("", "virtio_mmio@a000000"),
        i2c=None,
    ),
    Board(
        name="qemu_virt_riscv64",
        arch=riscv64,
        paddr_top=0xA_0000_000,
        serial=DriverDouble("ns16550a", "soc/serial@10000000"),
        timer=DriverDouble("google,goldfish-rtc", "soc/rtc@101000"),
        ethernet=DriverDouble("", "soc/virtio_mmio@10001000"),
        blk=DriverDouble("", "soc/virtio_mmio@10002000"),
        partition=0,
        i2c=None,
    ),
    Board(
        name="rock3b",
        arch=aarch64,
        paddr_top=0xEC000000,
        serial=DriverDouble("snps,dw-apb-uart", "serial@fe660000"),
        timer=DriverDouble("rockchip,rk3568-timer", "rktimer@fe5f0000"),
        ethernet=DriverDouble("", "ethernet@fe2a0000"),
        baud_rate=1500000,
    ),
    Board(
        name="rpi4b_1gb",
        arch=aarch64,
        paddr_top=0x2_000_000,
        serial=DriverDouble("brcm,bcm2835-aux-uart", "soc/serial@7e215040"),
        timer=DriverDouble("brcm,bcm2835-system-timer", "soc/timer@7e003000"),
        ethernet=DriverDouble("", "scb/ethernet@7d580000"),
    ),
    Board(
        name="serengeti",
        arch=riscv64,
        paddr_top=0x90000000,
        serial=DriverDouble("ns16550a", "soc/serial@3002000"),
        i2c=DriverDouble("eth,i2c", "soc/i2c@3003000"),
        timer=DriverDouble("pulp,apb_timer", "soc/timer@300B000"),
    ),
    Board(
        name="star64",
        arch=riscv64,
        paddr_top=0x100000000,
        serial=DriverDouble("starfive,jh7110-uart", "soc/serial@10000000"),
        timer=DriverDouble("starfive,jh7110-timer", "soc/timer@13050000"),
        ethernet=DriverDouble("", "soc/ethernet@16030000"),
    ),
    Board(
        name="zcu102",
        arch=aarch64,
        paddr_top=0x80000000,
        timer=DriverDouble("cdns,ttc", "axi/timer@ff140000"),
        serial=DriverDouble("xlnx,zynqmp-uart", "axi/serial@ff000000"),
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
