# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
import struct
import random
import json
from dataclasses import dataclass
from typing import List, Tuple
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel

# Should this be hard coded?
max_cores = 4

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
        return struct.pack("<qB", self.cycle_counters, self.ch_init)


class BenchmarkClientConfig:
    def __init__(self, ch_start: int, ch_stop: int, num_cores: int, cycle_counters: List[int]):
        self.ch_start = ch_start
        self.ch_stop = ch_stop
        self.num_cores = num_cores
        self.cycle_counters = cycle_counters
    '''
        Matches struct definition:
        {
            uint8_t;
            uint8_t;
            uint8_t;
            void *;
        }
    '''
    def serialise(self) -> bytes:
        pack_str = "<BBB" + "q" * max_cores
        for i in range(max_cores - len(self.cycle_counters)):
            self.cycle_counters.append(0)
        return struct.pack(pack_str, self.ch_start, self.ch_stop, self.num_cores, *self.cycle_counters)


class BenchmarkConfig:
    def __init__(self, ch_rx_start: int, ch_tx_start: int, ch_rx_stop: int, ch_tx_stop: int, ch_init: int, core: int, last_core: bool, children: List[Tuple[int, str]]):
        self.ch_rx_start = ch_rx_start
        self.ch_tx_start = ch_tx_start
        self.ch_rx_stop = ch_rx_stop
        self.ch_tx_stop = ch_tx_stop
        self.ch_init = ch_init
        self.core = core
        self.last_core = last_core
        self.children = children

    def serialise(self) -> bytes:
        child_config_format = "c" * 65
        pack_str = "<BBBBBB?B" + child_config_format * 64
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
            pack_str, self.ch_rx_start, self.ch_tx_start,
            self.ch_rx_stop, self.ch_tx_stop, self.ch_init, 
            self.core, self.last_core, len(self.children), *child_bytes_list
        )

# fix lambda type
def generate(sdf_file: str, output_dir: str, dtb: DeviceTree, get_pd_core):
    uart_node = dtb.node(board.serial)
    assert uart_node is not None
    ethernet_node = dtb.node(board.ethernet)
    assert ethernet_node is not None
    timer_node = dtb.node(board.timer)
    assert uart_node is not None

    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=101, cpu=get_pd_core("timer_driver"))
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)

    uart_driver = ProtectionDomain("uart_driver", "uart_driver.elf", priority=100, cpu=get_pd_core("uart_driver"))
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=99, cpu=get_pd_core("serial_virt_tx"))
    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx)

    ethernet_driver = ProtectionDomain(
        "ethernet_driver", "eth_driver.elf", priority=101, budget=100, period=400, cpu=get_pd_core("ethernet_driver")
    )

    net_virt_tx = ProtectionDomain("net_virt_tx", "network_virt_tx.elf", priority=100, budget=20000, cpu=get_pd_core("net_virt_tx"))
    net_virt_rx = ProtectionDomain("net_virt_rx", "network_virt_rx.elf", priority=99, cpu=get_pd_core("net_virt_rx"))
    net_system = Sddf.Net(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)

    client0 = ProtectionDomain("client0", "lwip0.elf", priority=97, budget=20000, cpu=get_pd_core("client0"))
    client0_net_copier = ProtectionDomain(
        "client0_net_copier", "network_copy0.elf", priority=98, budget=20000, cpu=get_pd_core("client0_net_copier")
    )
    client1 = ProtectionDomain("client1", "lwip1.elf", priority=97, budget=20000, cpu=get_pd_core("client1"))
    client1_net_copier = ProtectionDomain(
        "client1_net_copier", "network_copy1.elf", priority=98, budget=20000, cpu=get_pd_core("client1_net_copier")
    )

    mac_random_part = random.randint(0, 0xfe)
    client0_mac_addr = f"52:54:01:00:00:{hex(mac_random_part)[2:]:0>2}"
    client1_mac_addr = f"52:54:01:00:00:{hex(mac_random_part + 1)[2:]:0>2}"
    assert client0_mac_addr != client1_mac_addr

    serial_system.add_client(client0)
    serial_system.add_client(client1)
    timer_system.add_client(client0)
    timer_system.add_client(client1)
    net_system.add_client_with_copier(client0, client0_net_copier, mac_addr=client0_mac_addr)
    net_system.add_client_with_copier(client1, client1_net_copier, mac_addr=client1_mac_addr)

    # Echo server protection domains
    child_pds = [
        uart_driver,
        serial_virt_tx,
        ethernet_driver,
        net_virt_tx,
        net_virt_rx,
        client0,
        client0_net_copier,
        client1,
        client1_net_copier,
        timer_driver,
    ]

    # Sort into cores
    core_to_pds = {}
    for pd in child_pds:
        core = get_pd_core(pd.name)
        if core in core_to_pds:
            core_to_pds[core].append(pd)
        else:
            core_to_pds[core] = [pd]

    # Allocate benchmark resources
    cores = []
    last_bench_pd = 0
    last_bench_idle_channel = 0
    last_bench_start_channel = 0
    last_bench_stop_channel = 0
    last_bench_children = 0
    bench_idle_configs = []
    bench_configs = []
    for core in sorted(core_to_pds):
        cores.append(core)
        
        # Create bench and idle pds for each active core
        bench_idle = ProtectionDomain("bench_idle" + str(core), "idle.elf", priority=1, cpu=core)
        sdf.add_pd(bench_idle)

        bench = ProtectionDomain("bench" + str(core), "benchmark.elf", priority=254, cpu=core)
        sdf.add_pd(bench)

        serial_system.add_client(bench)

        # Create formatted list of children
        bench_children = []
        for pd in core_to_pds[core]:
            child_id = bench.add_child_pd(pd)
            bench_children.append((child_id, pd.name))

        # Benchmark idle channels
        bench_idle_ch = Channel(bench_idle, bench)
        sdf.add_channel(bench_idle_ch)

        # Benchmark start and stop channels
        if last_bench_pd == 0:
            start_ch = Channel(client0, bench)
            stop_ch = Channel(client0, bench)
        else:
            start_ch = Channel(last_bench_pd, bench)
            stop_ch = Channel(last_bench_pd, bench)

        sdf.add_channel(start_ch)
        sdf.add_channel(stop_ch)

        # Add cycle counter memory regions for client and bench_idles
        cycle_counters_mr = MemoryRegion("cycle_counters" + str(core), 0x1000)
        sdf.add_mr(cycle_counters_mr)
        bench_idle.add_map(Map(cycle_counters_mr, 0x5_000_000, perms=Map.Perms(r=True, w=True)))
        client_cycle_count_vaddr = 0x20_000_000 + 0x1000 * (len(cores) - 1)
        client0.add_map(Map(cycle_counters_mr, client_cycle_count_vaddr, perms=Map.Perms(r=True, w=False)))

        # Create configs
        bench_idle_configs.append( BenchmarkIdleConfig(0x5_000_000, bench_idle_ch.pd_a_id))
        if last_bench_pd != 0:
            bench_configs.append(BenchmarkConfig(
                last_bench_start_channel.pd_b_id,
                start_ch.pd_a_id,
                last_bench_stop_channel.pd_b_id,
                stop_ch.pd_a_id,
                last_bench_idle_channel.pd_b_id,
                cores[-2],
                False,
                last_bench_children
            ))
        else:
            bench_client_config = BenchmarkClientConfig(
                start_ch.pd_a_id,
                stop_ch.pd_a_id,
                len(core_to_pds),
                list(((0x20_000_000 + 0x1000 * i) for i in range(len(core_to_pds))))
            )
        
        last_bench_pd = bench
        last_bench_idle_channel = bench_idle_ch
        last_bench_start_channel = start_ch
        last_bench_stop_channel = stop_ch
        last_bench_children = bench_children
    
    # Create last bench config
    bench_configs.append(BenchmarkConfig(
        last_bench_start_channel.pd_b_id,
        0,
        last_bench_stop_channel.pd_b_id,
        0,
        last_bench_idle_channel.pd_b_id,
        cores[-1],
        True,
        last_bench_children
    ))

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert net_system.connect()
    assert net_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

    for i in range(len(cores)):
        core = cores[i]
        with open(f"{output_dir}/benchmark_config" + str(core) + ".data", "wb+") as f:
            f.write(bench_configs[i].serialise())

        with open(f"{output_dir}/benchmark_idle_config" + str(core) + ".data", "wb+") as f:
            f.write(bench_configs[i].serialise())

    with open(f"{output_dir}/benchmark_client_config.data", "wb+") as f:
        f.write(bench_client_config.serialise())

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.xml())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--smp", required=False)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    if args.smp:
        with open(args.smp, "r") as core_alloc:
            core_json = json.load(core_alloc)
        pd_to_core = {}
        for pd in core_json["core_allocations"]:
            pd_to_core[pd["name"]] = int(pd["core"])
        get_pd_core = lambda name: pd_to_core[name]
    else:
        get_pd_core = lambda name: 0
    
    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb, get_pd_core)
