# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
import struct
import random
import json
import subprocess
import shutil
from os import path
from dataclasses import dataclass
from typing import List, Tuple, Callable
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

assert version('sdfgen').split(".")[1] == "24", "Unexpected sdfgen version"

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
        name="qemu_virt_riscv64",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0xa_0000_000,
        serial="soc/serial@10000000",
        timer="soc/rtc@101000",
        ethernet="soc/virtio_mmio@10008000"
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
Structs are serialised to match 64-bit alignment.
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
    def __init__(self, ch_start: int, ch_stop: int, cycle_counters: List[int]):
        self.ch_start = ch_start
        self.ch_stop = ch_stop
        self.cycle_counters = cycle_counters
    '''
        Matches struct definition:
        {
            uint8_t;
            uint8_t;
            uint8_t;
            void * [];
        }
    '''
    def serialise(self) -> bytes:
        # Padded for 64 bit alignment
        pack_str = "<BBBxxxxx" + "q" * len(self.cycle_counters)
        return struct.pack(pack_str, self.ch_start, self.ch_stop, len(self.cycle_counters), *self.cycle_counters)


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
    '''
        Matches struct definition:
        {
            uint8_t;
            uint8_t;
            uint8_t;
            uint8_t;
            uint8_t;
            uint8_t;
            uint8_t;
            bool;
            uint8_t;
            struct {
                char [64];
                uint8_t;
            } [64];
        }
    '''
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

# Adds ".elf" to elf strings
def copy_elf(source_elf: str, new_elf: str, elf_number = None):
    source_elf += ".elf"
    if elf_number != None:
        new_elf += str(elf_number)
    new_elf += ".elf"
    assert path.isfile(source_elf)
    return shutil.copyfile(source_elf, new_elf)

# Assumes ".elf" at the end of elf string, adds ".data" to data string
def update_elf_section(elf_name: str, section_name: str, data_name: str, data_number = None):
    if data_number != None:
        data_name += str(data_number)
    data_name += ".data"
    assert path.isfile(elf_name)
    assert path.isfile(data_name)
    assert subprocess.run([obj_copy, "--update-section", "." + section_name + "=" + data_name, elf_name]).returncode == 0

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree, get_core: Callable[[str], int]):
    uart_node = dtb.node(board.serial)
    assert uart_node is not None
    ethernet_node = dtb.node(board.ethernet)
    assert ethernet_node is not None
    timer_node = dtb.node(board.timer)
    assert timer_node is not None

    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=101, cpu=get_core("timer_driver"))
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)

    uart_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=100, cpu=get_core("serial_driver"))
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=99, cpu=get_core("serial_virt_tx"))
    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx)

    ethernet_driver = ProtectionDomain(
        "ethernet_driver", "eth_driver.elf", priority=101, budget=100, period=400, cpu=get_core("ethernet_driver")
    )

    net_virt_tx = ProtectionDomain("net_virt_tx", "network_virt_tx.elf", priority=100, budget=20000, cpu=get_core("net_virt_tx"))
    net_virt_rx = ProtectionDomain("net_virt_rx", "network_virt_rx.elf", priority=99, cpu=get_core("net_virt_rx"))
    net_system = Sddf.Net(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)

    client0_elf = copy_elf("echo", "echo", 0)
    client0 = ProtectionDomain("client0", client0_elf, priority=97, budget=20000, cpu=get_core("client0"))
    client0_net_copier_elf = copy_elf("network_copy", "network_copy", 0)
    client0_net_copier = ProtectionDomain(
        "client0_net_copier", client0_net_copier_elf, priority=98, budget=20000, cpu=get_core("client0_net_copier")
    )

    client1_elf = copy_elf("echo", "echo", 1)
    client1 = ProtectionDomain("client1", client1_elf, priority=97, budget=20000, cpu=get_core("client1"))
    client1_net_copier_elf = copy_elf("network_copy", "network_copy", 0)
    client1_net_copier = ProtectionDomain(
        "client1_net_copier", client1_net_copier_elf, priority=98, budget=20000, cpu=get_core("client1_net_copier")
    )

    serial_system.add_client(client0)
    serial_system.add_client(client1)
    timer_system.add_client(client0)
    timer_system.add_client(client1)
    net_system.add_client_with_copier(client0, client0_net_copier)
    net_system.add_client_with_copier(client1, client1_net_copier)

    client0_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, client0)
    client1_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, client1)

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

    # Sort pds into cores
    pds_by_core = {}
    for pd in child_pds:
        core = get_core(pd.name)
        if core in pds_by_core:
            pds_by_core[core].append(pd)
        else:
            pds_by_core[core] = [pd]
    num_cores = len(pds_by_core)

    # Allocate benchmark resources
    core_objs = [{} for _ in range(num_cores)]
    for i in range(num_cores):
        core = sorted(pds_by_core)[i]
        core_objs[i]["core"] = core

        # Create bench and idle pds for each active core
        core_objs[i]["idle_elf"] = copy_elf("idle", "idle", core)
        core_objs[i]["idle"] = ProtectionDomain("bench_idle" + str(core), core_objs[i]["idle_elf"], priority=1, cpu=core)
        sdf.add_pd(core_objs[i]["idle"])

        core_objs[i]["bench_elf"] = copy_elf("benchmark", "benchmark", core)
        core_objs[i]["bench"] = ProtectionDomain("bench" + str(core), core_objs[i]["bench_elf"], priority=254, cpu=core)
        sdf.add_pd(core_objs[i]["bench"])
        serial_system.add_client(core_objs[i]["bench"])

        # Create formatted list of children
        core_objs[i]["children"] = []
        for pd in pds_by_core[core]:
            child_id = core_objs[i]["bench"].add_child_pd(pd)
            core_objs[i]["children"].append((child_id, pd.name))

        # Benchmark idle channels
        core_objs[i]["init_ch"] = Channel(core_objs[i]["idle"], core_objs[i]["bench"])
        sdf.add_channel(core_objs[i]["init_ch"])

        # Benchmark start and stop channels
        if i == 0:
            core_objs[i]["start_ch"] = Channel(client0, core_objs[i]["bench"])
            core_objs[i]["stop_ch"] = Channel(client0, core_objs[i]["bench"])
        else:
            core_objs[i]["start_ch"] = Channel(core_objs[i - 1]["bench"], core_objs[i]["bench"])
            core_objs[i]["stop_ch"] = Channel(core_objs[i - 1]["bench"], core_objs[i]["bench"])

        sdf.add_channel(core_objs[i]["start_ch"])
        sdf.add_channel(core_objs[i]["stop_ch"])

        # Add cycle counter memory regions for client and bench_idles
        cycle_counters_mr = MemoryRegion("cycle_counters" + str(core), 0x1000)
        sdf.add_mr(cycle_counters_mr)
        core_objs[i]["idle"].add_map(Map(cycle_counters_mr, 0x5_000_000, perms="rw"))
        client0.add_map(Map(cycle_counters_mr, 0x20_000_000 + 0x1000 * i, perms="r"))

        # Create configs
        core_objs[i]["idle_config"] = BenchmarkIdleConfig(0x5_000_000, core_objs[i]["init_ch"].pd_a_id)
        if i == 0:
            bench_client_config = BenchmarkClientConfig(
                core_objs[i]["start_ch"].pd_a_id,
                core_objs[i]["stop_ch"].pd_a_id,
                list(((0x20_000_000 + 0x1000 * i) for i in range(num_cores)))
            )
        else:
            core_objs[i - 1]["bench_config"] = BenchmarkConfig(
                core_objs[i - 1]["start_ch"].pd_b_id,
                core_objs[i]["start_ch"].pd_a_id,
                core_objs[i - 1]["stop_ch"].pd_b_id,
                core_objs[i]["stop_ch"].pd_a_id,
                core_objs[i - 1]["init_ch"].pd_b_id,
                core_objs[i - 1]["core"],
                False,
                core_objs[i - 1]["children"]
            )

    # Create last bench config
    core_objs[num_cores - 1]["bench_config"] = BenchmarkConfig(
        core_objs[num_cores - 1]["start_ch"].pd_b_id,
        0,
        core_objs[num_cores - 1]["stop_ch"].pd_b_id,
        0,
        core_objs[num_cores - 1]["init_ch"].pd_b_id,
        core_objs[num_cores - 1]["core"],
        True,
        core_objs[num_cores - 1]["children"]
    )

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert net_system.connect()
    assert net_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)
    assert client0_lib_sddf_lwip.connect()
    assert client0_lib_sddf_lwip.serialise_config(output_dir)
    assert client1_lib_sddf_lwip.connect()
    assert client1_lib_sddf_lwip.serialise_config(output_dir)

    section_name = "benchmark_client_config"
    data_name = "benchmark_client_config"
    with open(f"{output_dir}/" + data_name + ".data", "wb+") as f:
        f.write(bench_client_config.serialise())
    update_elf_section(client0_elf, section_name, data_name)

    for i in range(num_cores):
        core = core_objs[i]["core"]

        section_name = "serial_client_config"
        data_name = "serial_client_bench"
        update_elf_section(core_objs[i]["bench_elf"], section_name, data_name, core)

        section_name = "benchmark_config"
        data_name = "benchmark_config"
        with open(f"{output_dir}/" + data_name + str(core) + ".data", "wb+") as f:
            f.write(core_objs[i]["bench_config"].serialise())
        update_elf_section(core_objs[i]["bench_elf"], section_name, data_name, core)

        section_name = "benchmark_config"
        data_name = "benchmark_idle_config"
        with open(f"{output_dir}/" + data_name + str(core) + ".data", "wb+") as f:
            f.write(core_objs[i]["idle_config"].serialise())
        update_elf_section(core_objs[i]["idle_elf"], section_name, data_name, core)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--objcopy", required=True)
    parser.add_argument("--smp", required=False)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    global obj_copy
    obj_copy = args.objcopy
    if args.smp:
        with open(args.smp, "r") as core_alloc:
            core_dict = json.load(core_alloc)
        get_core = lambda name: core_dict[name]
    else:
        get_core = lambda name: 0

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb, get_core)
