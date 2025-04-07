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
        name="qemu_virt_aarch64",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x6_0000_000,
        serial="pl011@9000000",
        timer="timer",
        ethernet="virtio_mmio@a003e00"
    ),
    Board(
        name="odroidc2",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x60000000,
        serial="soc/bus@c8100000/serial@4c0",
        timer="soc/bus@c1100000/watchdog@98d0",
        ethernet="soc/ethernet@c9410000"
    ),
    Board(
        name="odroidc4",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x60000000,
        serial="soc/bus@ff800000/serial@3000",
        timer="soc/bus@ffd00000/watchdog@f0d0",
        ethernet="soc/ethernet@ff3f0000"
    ),
    Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/serial@30860000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet="soc@0/bus@30800000/ethernet@30be0000"
    ),
    Board(
        name="imx8mm_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/spba-bus@30800000/serial@30890000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet="soc@0/bus@30800000/ethernet@30be0000"
    ),
    Board(
        name="imx8mp_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/spba-bus@30800000/serial@30890000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet="soc@0/bus@30800000/ethernet@30be0000"
    ),
    Board(
        name="imx8mq_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70000000,
        serial="soc@0/bus@30800000/serial@30860000",
        timer="soc@0/bus@30000000/timer@302d0000",
        ethernet="soc@0/bus@30800000/ethernet@30be0000"
    ),
]

"""
Below are classes to serialise into custom configuration for the benchmarking component.
All serialised definitions are little endian and pointers are 64-bit integers.
"""


class BenchmarkIdleConfig:
    def __init__(self, cycle_counters: int, ch_init: int):
        self.cycle_counters = cycle_counters
        self.ch_init = ch_init

    '''
        Matches struct definition:
        {
            void *;
            uint8_t;
        }
    '''
    def serialise(self) -> bytes:
        return struct.pack("<qc", self.cycle_counters, self.ch_init.to_bytes(1, "little"))


class BenchmarkClientConfig:
    def __init__(self, cycle_counters: int, ch_start: int, ch_stop: int):
        self.cycle_counters = cycle_counters
        self.ch_start = ch_start
        self.ch_stop = ch_stop

    '''
        Matches struct definition:
        {
            void *;
            uint8_t;
            uint8_t;
        }
    '''
    def serialise(self) -> bytes:
        return struct.pack("<qBB", self.cycle_counters, self.ch_start, self.ch_stop)


class BenchmarkConfig:
    def __init__(self, ch_start: int, ch_stop: int, ch_init: int, children: List[Tuple[int, str]]):
        self.ch_start = ch_start
        self.ch_stop = ch_stop
        self.ch_init = ch_init
        self.children = children

    def serialise(self) -> bytes:
        child_config_format = "c" * 65
        pack_str = "<BBBB" + child_config_format * 64
        child_bytes = bytearray()
        for child in self.children:
            c_name = child[1].encode("utf-8")
            c_name_padded = c_name.ljust(64, b'\0')
            assert len(c_name_padded) == 64
            child_bytes.extend(c_name_padded)
            child_bytes.extend(child[0].to_bytes(1, "little"))

        child_bytes = child_bytes.ljust(64 * 65, b'\0')

        child_bytes_list = [x.to_bytes(1, "little") for x in child_bytes]

        return struct.pack(
            pack_str, self.ch_start, self.ch_stop,
            self.ch_init, len(self.children), *child_bytes_list
        )

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree, num_clients: int, target_client: int):
    uart_node = dtb.node(board.serial)
    assert uart_node is not None
    ethernet_node = dtb.node(board.ethernet)
    assert ethernet_node is not None
    timer_node = dtb.node(board.timer)
    assert timer_node is not None

    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=101)
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)

    uart_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=100)
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=99)
    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx)

    ethernet_driver = ProtectionDomain(
        "ethernet_driver", "eth_driver.elf", priority=101, budget=100, period=400
    )
    net_virt_tx = ProtectionDomain("net_virt_tx", "network_virt_tx.elf", priority=100, budget=20000)
    net_virt_rx = ProtectionDomain("net_virt_rx", "network_virt_rx.elf", priority=99)
    net_system = Sddf.Net(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)

    bench_idle = ProtectionDomain("bench_idle", "idle.elf", priority=1)
    bench = ProtectionDomain("bench", "benchmark.elf", priority=254)

    serial_system.add_client(bench)

    benchmark_pds = [
        uart_driver,
        serial_virt_tx,
        ethernet_driver,
        net_virt_tx,
        net_virt_rx,
        timer_driver,
    ]
    pds = [
        bench_idle,
        bench,
    ]
    bench_children = []
    for pd in benchmark_pds:
        child_id = bench.add_child_pd(pd)
        bench_children.append((child_id, pd.name))
    for pd in pds:
        sdf.add_pd(pd)

    bench_idle_ch = Channel(bench_idle, bench)
    sdf.add_channel(bench_idle_ch)

    cycle_counters_mr = MemoryRegion("cycle_counters", 0x1000)
    sdf.add_mr(cycle_counters_mr)

    ip_collector = ProtectionDomain(f"ip_collector", f"ip_collector.elf", priority=100)
    sdf.add_pd(ip_collector)
    timer_system.add_client(ip_collector)
    serial_system.add_client(ip_collector)
    ip_pool_vaddr = 0x20_000_000
    with open(f"{output_dir}/ip_collector_config.data", "wb+") as f:
        f.write(struct.pack("<qB", ip_pool_vaddr, num_clients))

    for i in range(num_clients):
        # TODO: give different priorities to clients
        client = ProtectionDomain(f"client{i}", f"echo{i}.elf", priority=97, budget=20000)
        client_net_copier = ProtectionDomain(
            f"client{i}_net_copier", f"network_copy{i}.elf", priority=98, budget=20000
        )

        if i == target_client:
            client.add_map(Map(cycle_counters_mr, 0x20_000_000, perms="rw"))

            # Benchmark START channel
            bench_start_ch = Channel(client, bench)
            sdf.add_channel(bench_start_ch)
            # Benchmark STOP channel
            bench_stop_ch = Channel(client, bench)
            sdf.add_channel(bench_stop_ch)

            child_id = bench.add_child_pd(client)
            bench_children.append((child_id, client.name))

            child_id = bench.add_child_pd(client_net_copier)
            bench_children.append((child_id, client_net_copier.name))

            serial_system.add_client(client)
        else:
            sdf.add_pd(client)
            sdf.add_pd(client_net_copier)

        # Create shared ip pool to mitigate necessity of connecting every client to serial subsystem
        ip_mr = MemoryRegion(f"ip_pool_client{i}", 0x1000)
        ip_vaddr = 0x30_000_000
        sdf.add_mr(ip_mr)
        client.add_map(Map(ip_mr, ip_vaddr, perms="rw"))
        with open(f"{output_dir}/client_config_{i}.data", "wb+") as f:
            f.write(struct.pack("<qB", ip_vaddr, i))

        ip_collector.add_map(Map(ip_mr, ip_pool_vaddr + 0x1000 * i, perms="rw"))

        timer_system.add_client(client)
        net_system.add_client_with_copier(client, client_net_copier)

        client_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, client)
        assert client_lib_sddf_lwip.connect()
        assert client_lib_sddf_lwip.serialise_config(output_dir)

    bench_idle.add_map(Map(cycle_counters_mr, 0x5_000_000, perms="rw"))
    bench_idle_config = BenchmarkIdleConfig(0x5_000_000, bench_idle_ch.pd_a_id)

    bench_client_config = BenchmarkClientConfig(
        0x20_000_000,
        bench_start_ch.pd_a_id,
        bench_stop_ch.pd_a_id
    )

    benchmark_config = BenchmarkConfig(
        bench_start_ch.pd_b_id,
        bench_stop_ch.pd_b_id,
        bench_idle_ch.pd_b_id,
        bench_children
    )


    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert net_system.connect()
    assert net_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

    with open(f"{output_dir}/benchmark_config.data", "wb+") as f:
        f.write(benchmark_config.serialise())

    with open(f"{output_dir}/benchmark_idle_config.data", "wb+") as f:
        f.write(bench_idle_config.serialise())

    with open(f"{output_dir}/benchmark_client_config.data", "wb+") as f:
        f.write(bench_client_config.serialise())

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--num-clients", required=True, type=int)
    parser.add_argument("--target-client", required=True, type=int)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb, args.num_clients, args.target_client)
