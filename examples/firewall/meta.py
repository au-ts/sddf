# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
import struct
import random
from dataclasses import dataclass
from typing import List, Tuple
from sdfgen import SystemDescription, Sddf, DeviceTree, LionsOs

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel


@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    serial: str
    timer: str
    ethernet: str
    ethernet1: str


BOARDS: List[Board] = [
    Board(
        name="imx8mp_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/spba-bus@30800000/serial@30890000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet="soc@0/bus@30800000/ethernet@30be0000",
        ethernet1="soc@0/bus@30800000/ethernet@30bf0000"
    ),
]

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    uart_node = dtb.node(board.serial)
    assert uart_node is not None
    ethernet_node = dtb.node(board.ethernet)
    assert ethernet_node is not None
    ethernet_node1 = dtb.node(board.ethernet1)
    assert ethernet_node1 is not None
    timer_node = dtb.node(board.timer)
    assert uart_node is not None

    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=101)
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)

    uart_driver = ProtectionDomain("uart_driver", "uart_driver.elf", priority=100)
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=99)
    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx)

    ethernet_driver = ProtectionDomain(
        "ethernet_driver", "eth_driver.elf", priority=101, budget=100, period=400
    )
    ethernet_driver1 = ProtectionDomain(
        "ethernet_driver_dwmac", "eth_driver_dwmac.elf", priority=101, budget=100, period=400
    )

    net_virt_tx = ProtectionDomain("net_virt_tx", "network_virt_tx.elf", priority=100, budget=20000)
    net_virt_rx = ProtectionDomain("net_virt_rx", "network_virt_rx.elf", priority=99)
    net_virt_tx1 = ProtectionDomain("net_virt_tx_1", "network_virt_tx_1.elf", priority=100, budget=20000)
    net_virt_rx1 = ProtectionDomain("net_virt_rx_1", "network_virt_rx_1.elf", priority=99)

    net_system = Sddf.Net(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)
    net_system2 = Sddf.Net(sdf, ethernet_node1, ethernet_driver1, net_virt_tx1, net_virt_rx1)

    routing = ProtectionDomain("routing", "routing.elf", priority=97, budget=20000)
    arp_responder = ProtectionDomain("arp_responder", "arp_responder.elf", priority=95, budget=20000)
    arp_requester = ProtectionDomain("arp_requester", "arp_requester.elf", priority=98, budget=20000)
    firewall = LionsOs.Firewall(sdf, net_system, net_system2, routing, arp_responder, arp_requester, 157)

    # @kwinter: These need to be added to second net_system
    serial_system.add_client(routing)

    serial_system.add_client(arp_responder)
    # @kwinter: Internal arp needs timer to handle stale ARP cache entries.
    timer_system.add_client(arp_requester)

    pds = [
        uart_driver,
        serial_virt_tx,
        ethernet_driver,
        ethernet_driver1,
        net_virt_tx,
        net_virt_tx1,
        net_virt_rx,
        net_virt_rx1,
        routing,
        arp_responder,
        arp_requester,
        timer_driver,
    ]

    for pd in pds:
        sdf.add_pd(pd)

    assert firewall.connect()
    assert firewall.serialise_config(output_dir)
    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert net_system.connect()
    assert net_system.serialise_config(output_dir)
    assert net_system2.connect()
    assert net_system2.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == '__main__':
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
