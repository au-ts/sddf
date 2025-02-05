# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
import struct
import random
from dataclasses import dataclass
from typing import List, Tuple
from sdfgen import SystemDescription, Sddf, DeviceTree

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


BOARDS: List[Board] = [
    Board(
        name="imx8mp_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/spba-bus@30800000/serial@30890000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet1="soc@0/bus@30800000/ethernet@30be0000"
        ethernet2="soc@0/bus@30800000/ethernet@30bf0000"
    ),
]

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    uart_node = dtb.node(board.serial)
    assert uart_node is not None
    ethernet_node = dtb.node(board.ethernet2)
    assert ethernet_node is not None
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
    net_virt_tx = ProtectionDomain("net_virt_tx", "network_virt_tx.elf", priority=100, budget=20000)
    net_virt_rx = ProtectionDomain("net_virt_rx", "network_virt_rx.elf", priority=99)
    net_system = Sddf.Network(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)

    proxy_arp = ProtectionDomain("proxy_arp", "proxy_arp.elf", priority=97, budget=20000)
    proxy_arp_net_copier = ProtectionDomain(
        "proxy_arp_net_copier", "network_copy.elf", priority=98, budget=20000
    )

    routing = ProtectionDomain("routing", "routing.elf", priority=97, budget=20000)
    routing_net_copier = ProtectionDomain(
        "routing_net_copier", "network_copy0.elf", priority=98, budget=20000
    )

    internal_arp = ProtectionDomain("internal_arp", "internal_arp.elf", priority=95, budget=20000)
    internal_arp_net_copier = ProtectionDomain(
        "internal_arp_net_copier", "network_copy1.elf", priority=96, budget=20000
    )

    mac_random_part = random.randint(0, 0xfe)
    proxy_arp_mac_addr = f"52:54:01:00:00:{hex(mac_random_part)[2:]:0>2}"
    # @kwinter: Is there anyway to get the MAC addr of the routing component in the proxy arp component?
    routing_mac_addr = f"52:54:01:00:00:{hex(mac_random_part)[2:]:0>2}"
    internal_arp_mac_addr = f"52:54:01:00:00:{hex(mac_random_part)[2:]:0>2}"

    serial_system.add_client(proxy_arp)
    net_system.add_client_with_copier(proxy_arp, proxy_arp_net_copier, mac_addr=proxy_arp_mac_addr)

    # @kwinter: These need to be added to second net_system
    serial_system.add_client(routing)
    net_system.add_client_with_copier(routing, routing_net_copier, mac_addr=routing_mac_addr)

    serial_system.add_client(internal_arp)
    # @kwinter: Internal arp needs timer to handle stale ARP cache entries.
    timer_system.add_client(internal_arp)
    net_system.add_client_with_copier(internal_arp, internal_arp_net_copier, mac_addr=internal_arp_mac_addr)

    pds = [
        uart_driver,
        serial_virt_tx,
        ethernet_driver,
        net_virt_tx,
        net_virt_rx,
        proxy_arp,
        proxy_arp_net_copier,
        routing,
        routing_net_copier,
        internal_arp,
        internal_arp_net_copier,
        timer_driver,
    ]

    for pd in pds:
        sdf.add_pd(pd)

    routing_table = MemoryRegion("routing_table", 0x4000)
    sdf.add_mr(routing_table)
    routing.add_map(Map(routing_table, 0x3_000_000, perms=Map.Perms(r=True, w=True)))
    proxy_arp.add_map(Map(routing_table, 0x10_000_000, perms=Map.Perms(r=True, w=False)))

    arp_table = MemoryRegion("arp_table", 0x4000)
    sdf.add_mr(arp_table)
    routing.add_map(Map(arp_table, 0x3_500_000, perms=Map.Perms(r=True, w=False)))
    internal_arp.add_map(Map(arp_table, 0x10_500_000, perms=Map.Perms(r=True, w=True)))

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert net_system.connect()
    assert net_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.xml())


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
