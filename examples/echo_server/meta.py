# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import sys, os
import argparse
import struct
import json
import subprocess
import shutil
from typing import List, Tuple, Callable, Optional
from acacia import System, ProtectionDomain, MemoryRegion, Channel, DeviceTreeBlob, Map, x86_64, SchedulingProperties

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../"))
from acacia_sddf import BOARDS, sDDFEthernet, sDDFSerial, sDDFTimer


"""
Below are classes to serialise into custom configuration for the benchmarking component.
All serialised definitions are little endian and pointers are 64-bit integers.
Structs are serialised to match 64-bit alignment.
# TODO: replace with Acacia
"""


class BenchmarkIdleConfig:
    def __init__(self, cycle_counters: int, ch_init: int):
        self.cycle_counters = cycle_counters
        self.ch_init = ch_init

    """
        Matches struct definition:
        {
            void *;
            uint8_t;
        }
    """

    def serialise(self) -> bytes:
        return struct.pack(
            "<qc", self.cycle_counters, self.ch_init.to_bytes(1, "little")
        )


class BenchmarkClientConfig:
    def __init__(self, ch_start: int, ch_stop: int, cycle_counters: List[int]):
        self.cycle_counters = cycle_counters
        self.ch_start = ch_start
        self.ch_stop = ch_stop

    """
        Matches struct definition:
        {
            uint8_t;
            uint8_t;
            uint8_t;
            void * [];
        }
    """

    def serialise(self) -> bytes:
        # Padded for 64 bit alignment
        pack_str = "<BBBxxxxx" + "q" * len(self.cycle_counters)
        return struct.pack(
            pack_str,
            self.ch_start,
            self.ch_stop,
            len(self.cycle_counters),
            *self.cycle_counters,
        )


class BenchmarkConfig:
    def __init__(
        self,
        ch_rx_start: int,
        ch_tx_start: int,
        ch_rx_stop: int,
        ch_tx_stop: int,
        ch_init: int,
        core: int,
        last_core: bool,
        children: List[Tuple[int, str]],
        pmu_events: List[int],
    ):
        self.ch_rx_start = ch_rx_start
        self.ch_tx_start = ch_tx_start
        self.ch_rx_stop = ch_rx_stop
        self.ch_tx_stop = ch_tx_stop
        self.ch_init = ch_init
        self.core = core
        self.last_core = last_core
        self.children = children
        self.pmu_events = pmu_events

    """
        Matches struct definition:
        {
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
            uint8_t [6];
            uint8_t;
        }
    """

    def serialise(self) -> bytes:
        child_config_format = "c" * 65
        pack_str = "<BBBBBB?B" + child_config_format * 64 + "BBBBBBB"
        child_bytes = bytearray()
        for child in self.children:
            c_name = child[1].encode("utf-8")
            c_name_padded = c_name.ljust(64, b"\0")
            assert len(c_name_padded) == 64
            child_bytes.extend(c_name_padded)
            child_bytes.extend(child[0].to_bytes(1, "little"))

        child_bytes = child_bytes.ljust(64 * 65, b"\0")

        child_bytes_list = [x.to_bytes(1, "little") for x in child_bytes]

        num_pmu_events = len(self.pmu_events)
        assert num_pmu_events <= 6
        self.pmu_events.extend(0 for i in range(6 - num_pmu_events))

        return struct.pack(
            pack_str,
            self.ch_rx_start,
            self.ch_tx_start,
            self.ch_rx_stop,
            self.ch_tx_stop,
            self.ch_init,
            self.core,
            self.last_core,
            len(self.children),
            *child_bytes_list,
            *self.pmu_events,
            num_pmu_events,
        )


# Adds ".elf" to elf strings
def copy_elf(source_elf: str, new_elf: str, elf_number=None):
    source_elf += ".elf"
    if elf_number != None:
        new_elf += str(elf_number)
    new_elf += ".elf"
    assert os.path.isfile(source_elf)
    return shutil.copyfile(source_elf, new_elf)


# Assumes elf string has ".elf" suffix, adds ".data" to data string
# TODO: replace this with configstructs!
def update_elf_section(
    elf_name: str, section_name: str, data_name: str, data_number=None
):
    assert os.path.isfile(elf_name)
    if data_number != None:
        data_name += str(data_number)
    data_name += ".data"
    assert os.path.isfile(data_name)
    assert (
        subprocess.run(
            [
                obj_copy,
                "--update-section",
                "." + section_name + "=" + data_name,
                elf_name,
            ]
        ).returncode
        == 0
    )


def generate(
    sdf_file: str,
    output_dir: str,
    dtb: Optional[DeviceTreeBlob],
    get_core: Callable[[str], int],
    pmu_event_ids: List[int],
):

    timer = sDDFTimer(
        sdf,
        board.timer.compatible,
        board.timer.node_path,
        cpu=get_core("timer_driver")
    )
    serial = sDDFSerial(
        sdf,
        board.serial.compatible,
        board.serial.node_path,
        cpu=get_core("serial_driver"),
        driver_prio=201,
        virt_tx_prio=200,
        allow_rx=False,
        enable_color=False,
        baud_rate=board.baud_rate if board.baud_rate else 115200,
    )

    ethernet = sDDFEthernet(
        sdf,
        board.ethernet.compatible,
        board.ethernet.node_path,
        driver_prio=101,
        virt_tx_prio=100,
        virt_rx_prio=99,
        cpu=get_core("ethernet_driver"), # Assign everything to driver prio initially
    )

    # Reassign components to whatever CPU is specified for benchmark
    for pd, core in (
        (ethernet.virt_rx, get_core("net_virt_rx")),
        (ethernet.virt_tx, get_core("net_virt_tx"))):
        pd.cpu = core

    if board.name == "star64":
        # For ethernet reset, the Pine64 Star64 driver needs access to the
        # clock controller. We do not have a clock driver for this platform so the
        # ethernet driver does it directly.
        clock_controller = MemoryRegion(
            sdf, "clock_controller", 0x10_000, paddr=0x17000000
        )
        ethernet.driver.add_map(
            Map(clock_controller, 0x3000000, perms="rw", cached=False)
        )
    elif board.name == "rock3b":
        # For ethernet reset, we need to disable areset_gmac0 which is left high by u-boot
        clock_controller = MemoryRegion(
            sdf, "clock_controller", 0x10_000, paddr=0xFDD20000
        )
        ethernet.driver.add_map(
            Map(clock_controller, 0x3000000, perms="rw", cached=False)
        )
    elif board.name == "rpi4b_1gb":
        # Ethernet driver requires timer access to wait for reconfiguration
        timer.add_client(ethernet.driver)

        mbox = MemoryRegion(sdf, "mbox", 0x10_000, paddr=0xFE00B000)
        ethernet.driver.add_map(Map(mbox, 0x3000000, perms="rw", cached=False))

    if board.arch == x86_64:
        hw_net_rings = SystemDescription.MemoryRegion(
            sdf, "hw_net_rings", 65536, paddr=0x7A000000
        )
        hw_net_rings_map = SystemDescription.Map(hw_net_rings, 0x7000_0000, "rw")
        ethernet.driver.add_map(hw_net_rings_map)

        virtio_net_regs = SystemDescription.MemoryRegion(
            sdf, "virtio_net_regs", 0x4000, paddr=0xFE000000
        )
        virtio_net_regs_map = SystemDescription.Map(
            virtio_net_regs, 0x6000_0000, "rw", cached=False
        )
        ethernet.driver.add_map(virtio_net_regs_map)

        virtio_net_irq = SystemDescription.IrqIoapic(
            ioapic_id=0, pin=11, vector=1, id=16
        )
        ethernet.driver.add_irq(virtio_net_irq)

        pci_config_address_port = SystemDescription.IoPort(0xCF8, 4, 1)
        ethernet.driver.add_ioport(pci_config_address_port)

        pci_config_data_port = SystemDescription.IoPort(0xCFC, 4, 2)
        ethernet.driver.add_ioport(pci_config_data_port)

    client0_elf = copy_elf("echo", "echo", 0)
    client0 = ProtectionDomain(
        sdf,
        "client0",
        client0_elf,
        scheduling=SchedulingProperties(priority=97, budget=20000),
        cpu=get_core("client0")
    )
    client1_elf = copy_elf("echo", "echo", 1)
    client1 = ProtectionDomain(
        sdf,
        "client1",
        client1_elf,
        scheduling=SchedulingProperties(priority=97, budget=20000),
        cpu=get_core("client1")
    )
    client1_net_copier_elf = copy_elf("network_copy", "network_copy", 0)
    client0_net_copier_elf = copy_elf("network_copy", "network_copy", 0)

    client0_net_copier = ProtectionDomain(
        sdf,
        "client0_net_copier",
        client0_net_copier_elf,
        scheduling=SchedulingProperties(priority=98, budget=20000),
        cpu=get_core("client0_net_copier"),
    )
    client1_net_copier = ProtectionDomain(
        sdf,
        "client1_net_copier",
        client1_net_copier_elf,
        scheduling=SchedulingProperties(priority=98, budget=20000),
        cpu=get_core("client1_net_copier"),
    )
    serial.add_client(client0)
    serial.add_client(client1)
    timer.add_client(client0)
    timer.add_client(client1)
    net_system.add_client_with_copier(client0, client0_net_copier)
    net_system.add_client_with_copier(client1, client1_net_copier)

    client0_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, client0)
    client1_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, client1)

    # Echo server protection domains
    child_pds = [
        uart_driver,
        serial_virt_tx,
        ethernet.driver,
        net_virt_tx,
        net_virt_rx,
        client0,
        client0_net_copier,
        client1,
        client1_net_copier,
        timer_driver,
    ]

    # Sort pds into cores, ensure all PDs have a core allocation
    pds_per_core = {}
    for pd in child_pds:
        try:
            core = get_core(pd.name)
        except:
            raise ValueError(
                f"PD {pd.name} is missing from your core allocation configuration file!"
            )
        if core in pds_per_core:
            pds_per_core[core].append(pd)
        else:
            pds_per_core[core] = [pd]
    num_cores = len(pds_per_core)

    # Allocate benchmarking resources
    core_objs = [{} for _ in range(num_cores)]
    for i in range(num_cores):
        core = sorted(pds_per_core)[i]
        core_objs[i]["core"] = core

        # Create benchmark and idle PDs for each active core
        core_objs[i]["idle_elf"] = copy_elf("idle", "idle", core)
        core_objs[i]["idle_pd"] = ProtectionDomain(
            f"bench_idle{core}", core_objs[i]["idle_elf"], priority=1, cpu=core
        )
        sdf.add_pd(core_objs[i]["idle_pd"])

        core_objs[i]["bench_elf"] = copy_elf("benchmark", "benchmark", core)
        core_objs[i]["bench_pd"] = ProtectionDomain(
            f"bench{core}", core_objs[i]["bench_elf"], priority=254, cpu=core
        )
        sdf.add_pd(core_objs[i]["bench_pd"])

        # Benchmark PD requires serial output
        serial.add_client(core_objs[i]["bench_pd"])

        # Create formatted list of children for benchmark PD
        core_objs[i]["children"] = []
        for pd in pds_per_core[core]:
            child_id = core_objs[i]["bench_pd"].add_child_pd(pd)
            core_objs[i]["children"].append((child_id, pd.name))

        # Create benchmark to idle init channel
        core_objs[i]["init_ch"] = Channel(
            core_objs[i]["idle_pd"], core_objs[i]["bench_pd"]
        )
        sdf.add_channel(core_objs[i]["init_ch"])

        # Create benchmarking start and stop channels
        if i == 0:
            # First active core is notified by benchmarking client
            core_objs[i]["start_ch"] = Channel(client0, core_objs[i]["bench_pd"])
            core_objs[i]["stop_ch"] = Channel(client0, core_objs[i]["bench_pd"])
        else:
            # Other cores are notified by benchmark PD on previous core
            core_objs[i]["start_ch"] = Channel(
                core_objs[i - 1]["bench_pd"], core_objs[i]["bench_pd"]
            )
            core_objs[i]["stop_ch"] = Channel(
                core_objs[i - 1]["bench_pd"], core_objs[i]["bench_pd"]
            )

        sdf.add_channel(core_objs[i]["start_ch"])
        sdf.add_channel(core_objs[i]["stop_ch"])

        # Add cycle counter memory region for idle to share counts with benchmarking client
        cycle_counters_mr = MemoryRegion(sdf, f"cycle_counters{core}", 0x1000)
        core_objs[i]["idle_pd"].add_map(Map(cycle_counters_mr, 0x5_000_000, perms="rw"))
        client0.add_map(Map(cycle_counters_mr, 0x20_000_000 + 0x1000 * i, perms="r"))

        # Create configuration structures to be serialised
        core_objs[i]["idle_config"] = BenchmarkIdleConfig(
            0x5_000_000, core_objs[i]["init_ch"].pd_a_id
        )
        if i == 0:
            # We first create a config for the benchmarking client
            bench_client_config = BenchmarkClientConfig(
                core_objs[i]["start_ch"].pd_a_id,
                core_objs[i]["stop_ch"].pd_a_id,
                list(((0x20_000_000 + 0x1000 * i) for i in range(num_cores))),
            )
        else:
            # Then we create the config for the benchmark PD on the previous core
            core_objs[i - 1]["bench_config"] = BenchmarkConfig(
                core_objs[i - 1]["start_ch"].pd_b_id,
                core_objs[i]["start_ch"].pd_a_id,
                core_objs[i - 1]["stop_ch"].pd_b_id,
                core_objs[i]["stop_ch"].pd_a_id,
                core_objs[i - 1]["init_ch"].pd_b_id,
                core_objs[i - 1]["core"],
                False,
                core_objs[i - 1]["children"],
                pmu_event_ids,
            )

    # Finally create the last benchmark PD config
    core_objs[num_cores - 1]["bench_config"] = BenchmarkConfig(
        core_objs[num_cores - 1]["start_ch"].pd_b_id,
        0,
        core_objs[num_cores - 1]["stop_ch"].pd_b_id,
        0,
        core_objs[num_cores - 1]["init_ch"].pd_b_id,
        core_objs[num_cores - 1]["core"],
        True,
        core_objs[num_cores - 1]["children"],
        pmu_event_ids,
    )

    if board.name == "rpi4b_1gb":
        update_elf_section(
            "eth_driver.elf", "timer_client_config", "timer_client_ethernet.driver"
        )

    with open(f"{output_dir}/benchmark_client_config.data", "wb+") as f:
        f.write(bench_client_config.serialise())
    update_elf_section(
        client0_elf, "benchmark_client_config", "benchmark_client_config"
    )

    for i in range(num_cores):
        core = core_objs[i]["core"]
        update_elf_section(
            core_objs[i]["bench_elf"],
            "serial_client_config",
            "serial_client_bench",
            core,
        )

        with open(f"{output_dir}/benchmark_config{core}.data", "wb+") as f:
            f.write(core_objs[i]["bench_config"].serialise())
        update_elf_section(
            core_objs[i]["bench_elf"], "benchmark_config", "benchmark_config", core
        )

        with open(f"{output_dir}/benchmark_idle_config{core}.data", "wb+") as f:
            f.write(core_objs[i]["idle_config"].serialise())
        update_elf_section(
            core_objs[i]["idle_elf"], "benchmark_config", "benchmark_idle_config", core
        )

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


# ARM PMU event identifier dictionary:
#
# The pmu_event_table structure (defined in benchmark.c) lists the set of PMU
# events the system can be configured to track during a benchmark run. The
# python dictionary bench_pmu_events encodes this enum. For each enum event x:
#
# bench_pmu_events[x][0] = the enum value of x
# bench_pmu_events[x][1] = any ARM boards listed in BOARDS that DO NOT support
# benchmark tracking of event x
#
# Which PMU events are tracked can be configured by setting the make flag
# BENCH_PMU_EVENTS to a comma separated list of events.
#
# See the echo server README.md for more information, in particular if you wish
# to track a PMU event which is not currently listed.
bench_pmu_events = {
    "L1I_CACHE_MISS": (1, []),
    "L1I_TLB_MISS": (2, []),
    "L1D_CACHE_MISS": (3, []),
    "L1D_CACHE": (4, []),
    "L1D_TLB_MISS": (5, []),
    "LOAD_INSTRUCTIONS": (6, []),
    "STORE_INSTRUCTIONS": (7, []),
    "INSTRUCTIONS": (8, []),
    "BRANCH_MISPREDICT": (16, []),
    "CPU_CYCLES": (17, []),
    "MEM_ACCESS": (19, []),
    "CHAIN": (30, []),
    "STALL_FRONTEND_CACHE": (31, ["rpi4b_1gb"]),
    "STALL_FRONTEND_TLB": (32, ["rpi4b_1gb"]),
    "STALL_BACKEND_ILOCK": (33, ["rpi4b_1gb"]),
    "STALL_BACKEND_LD": (34, ["rpi4b_1gb"]),
    "STALL_BACKEND_ST": (35, ["rpi4b_1gb"]),
}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=False)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--objcopy", required=True)
    parser.add_argument("--smp", required=True)
    parser.add_argument("--bench_pmu_events", required=False)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    dtb = DeviceTreeBlob(args.dtb)
    sdf = System(board.arch, board.paddr_top, dtb)

    global obj_copy
    obj_copy = args.objcopy

    with open(args.smp, "r") as core_alloc:
        core_dict = json.load(core_alloc)
    get_core = lambda name: core_dict[name]


    if args.bench_pmu_events:
        pmu_events = args.bench_pmu_events.split(",")
    else:
        # If benchmarking PMU events are not provided, we use these default events
        pmu_events = [
            "INSTRUCTIONS",
            "CHAIN",
            "MEM_ACCESS",
            "CHAIN",
            "L1D_CACHE_MISS",
            "CHAIN",
        ]

    assert (
        len(pmu_events) <= 6
    ), "Supplied more than 6 benchmarking PMU events to track!"
    pmu_event_ids = []
    for i in range(len(pmu_events)):
        if not i % 2:
            assert (
                pmu_events[i] != "CHAIN"
            ), f"Chaining (overflow counting) can only be used by odd counters (selected counter {i})!"

        assert (
            pmu_events[i] in bench_pmu_events
        ), f"Selected PMU event {i} ({pmu_events[i]}) is not supported!"

        assert (
            args.board not in bench_pmu_events[pmu_events[i]][1]
        ), f"Selected PMU event {i} ({pmu_events[i]}) is not supported by board {args.board}!"

        pmu_event_ids.append(bench_pmu_events[pmu_events[i]][0])

    generate(args.sdf, args.output, dtb, get_core, pmu_event_ids)
