import sys, os
import argparse
import struct
import json
import re
import subprocess
import shutil
from typing import List, Tuple, Callable
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)
from board import BOARDS

assert version("sdfgen").split(".")[1] == "33", "Unexpected sdfgen version"  # enforced by board.py

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel

"""
Below are classes to serialise into custom configuration for the benchmarking component.
All serialised definitions are little endian and pointers are 64-bit integers.
Structs are serialised to match 64-bit alignment.
"""

class BenchmarkIdleConfig:
    def __init__(self, cycle_counters: int, ch_init: int):
        self.cycle_counters = cycle_counters
        self.ch_init = ch_init
        
    def serialise(self) -> bytes:
        return struct.pack(
            "<qc", self.cycle_counters, self.ch_init.to_bytes(1, "little")
        )


class BenchmarkClientConfig:
    def __init__(self, ch_start: int, ch_stop: int, cycle_counters: List[int]):
        self.cycle_counters = cycle_counters
        self.ch_start = ch_start
        self.ch_stop = ch_stop

    def serialise(self) -> bytes:
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
        self.pmu_events.extend(0 for _ in range(6 - num_pmu_events))

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


class IperfAppConfig:

    def __init__(self, client_id: int):
        self.client_id = client_id

    def serialise(self) -> bytes:
        return struct.pack("<B", self.client_id)


IPERF3_MAX_PEERS = 4


class IperfMultiConfig:

    def __init__(self, is_controller: int, listen_channel: int, peer_channels: List[int]):
        self.is_controller = is_controller
        self.listen_channel = listen_channel
        self.peer_channels = peer_channels

    def serialise(self) -> bytes:
        assert len(self.peer_channels) <= IPERF3_MAX_PEERS
        peers = bytes(self.peer_channels).ljust(IPERF3_MAX_PEERS, b"\0")
        return struct.pack(
            "<BBB" + str(IPERF3_MAX_PEERS) + "s",
            self.is_controller, len(self.peer_channels), self.listen_channel, peers
        )


def copy_elf(source_elf: str, new_elf: str, elf_number=None):
    source_elf += ".elf"
    if elf_number != None:
        new_elf += str(elf_number)
    new_elf += ".elf"
    assert os.path.isfile(source_elf)
    return shutil.copyfile(source_elf, new_elf)


def update_elf_section(elf_name: str, section_name: str, data_name: str, data_number=None):
    assert os.path.isfile(elf_name)
    if data_number is not None:
        data_name += str(data_number)
    data_name += ".data"
    assert os.path.isfile(data_name), f"missing {data_name}"
    assert (
        subprocess.run(
            [obj_copy, "--update-section", "." + section_name + "=" + data_name, elf_name]
        ).returncode
        == 0
    )


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree, core_dict: dict,
             pmu_event_ids: List[int]):
    get_core = lambda name: core_dict[name]

    client_indices = sorted(
        int(m.group(1))
        for k in core_dict
        if (m := re.fullmatch(r"client(\d+)", k))
    )
    assert client_indices, "core config must define at least client0"
    assert client_indices == list(range(len(client_indices))), \
        "clients must be numbered 0..N-1 contiguously"

    uart_node = dtb.node(board.serial)
    assert uart_node is not None
    ethernet_node = dtb.node(board.ethernet)
    assert ethernet_node is not None
    timer_node = dtb.node(board.timer)
    assert timer_node is not None


    timer_driver = ProtectionDomain(
        "timer_driver", "timer_driver.elf", priority=101, cpu=get_core("timer_driver")
    )
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)

    uart_driver = ProtectionDomain(
        "serial_driver", "serial_driver.elf", priority=100, cpu=get_core("serial_driver")
    )
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx", "serial_virt_tx.elf", priority=99, cpu=get_core("serial_virt_tx")
    )
    serial_virt_rx = ProtectionDomain(
        "serial_virt_rx", "serial_virt_rx.elf", priority=99, cpu=get_core("serial_virt_rx")
    )
    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx,
                                virt_rx=serial_virt_rx)

    ethernet_driver = ProtectionDomain(
        "ethernet_driver", "eth_driver.elf", priority=101, budget=100, period=400,
        cpu=get_core("ethernet_driver")
    )
    if board.name == "star64":
        clock_controller = MemoryRegion(sdf, "clock_controller", 0x10_000, paddr=0x17000000)
        sdf.add_mr(clock_controller)
        ethernet_driver.add_map(Map(clock_controller, 0x3000000, perms="rw"))

    net_virt_tx = ProtectionDomain(
        "net_virt_tx", "network_virt_tx.elf", priority=100, budget=20000,
        cpu=get_core("net_virt_tx")
    )
    net_virt_rx = ProtectionDomain(
        "net_virt_rx", "network_virt_rx.elf", priority=99, cpu=get_core("net_virt_rx")
    )
    net_system = Sddf.Net(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)

    # One iperf3 client + copier per clientN in the core config. The client ELF
    # is copied per-client so each copy can carry its own .iperf3_app_config.
    clients = []
    for i in client_indices:
        client_elf = copy_elf("iperf3_client", "iperf3_client", i)
        client_pd = ProtectionDomain(
            f"client{i}", client_elf, priority=98, budget=20000,
            cpu=get_core(f"client{i}"), stack_size=0x1000000
        )
        copier_elf = copy_elf("network_copy", "network_copy", i)
        copier_pd = ProtectionDomain(
            f"client{i}_net_copier", copier_elf, priority=97, budget=20000,
            cpu=get_core(f"client{i}_net_copier")
        )
        serial_system.add_client(client_pd)
        timer_system.add_client(client_pd)
        net_system.add_client_with_copier(client_pd, copier_pd)
        lwip = Sddf.Lwip(sdf, net_system, client_pd)
        clients.append({
            "i": i, "elf": client_elf, "pd": client_pd,
            "copier_elf": copier_elf, "copier_pd": copier_pd, "lwip": lwip,
        })

    # Multi-client coordination: client0 is the controller
    # A shared params region is mapped into every client at a fixed
    # vaddr and notifies each peer over a dedicated channel
    SHARED_PARAMS_VADDR = 0x30_000_000
    multi_cfg_by_i = {}
    if len(clients) > 1:
        shared_params_mr = MemoryRegion(sdf, "iperf3_shared_params", 0x1000)
        sdf.add_mr(shared_params_mr)
        for c in clients:
            c["pd"].add_map(Map(shared_params_mr, SHARED_PARAMS_VADDR, perms="rw"))
        controller = clients[0]["pd"]
        peer_channels = []
        for c in clients[1:]:
            ch = Channel(controller, c["pd"])
            sdf.add_channel(ch)
            peer_channels.append(ch.pd_a_id)
            multi_cfg_by_i[c["i"]] = IperfMultiConfig(0, ch.pd_b_id, [])
        multi_cfg_by_i[0] = IperfMultiConfig(1, 0, peer_channels)
    else:
        # Single client: it is its own controller with no peers.
        multi_cfg_by_i[clients[0]["i"]] = IperfMultiConfig(1, 0, [])

    # All application PDs become children of their core's benchmark PD.
    child_pds = [
        uart_driver, serial_virt_tx, serial_virt_rx, ethernet_driver, net_virt_tx,
        net_virt_rx, timer_driver,
    ]
    for c in clients:
        child_pds.append(c["pd"])
        child_pds.append(c["copier_pd"])

    # Group PDs by core.
    pds_per_core = {}
    for pd in child_pds:
        core = get_core(pd.name)
        pds_per_core.setdefault(core, []).append(pd)
    num_cores = len(pds_per_core)

    bench_client_pd = clients[0]["pd"]  # client0 drives + reports benchmarking

    # Per-core benchmark + idle PDs, chained start/stop across cores.
    core_objs = [{} for _ in range(num_cores)]
    for i in range(num_cores):
        core = sorted(pds_per_core)[i]
        core_objs[i]["core"] = core

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

        serial_system.add_client(core_objs[i]["bench_pd"])

        core_objs[i]["children"] = []
        for pd in pds_per_core[core]:
            child_id = core_objs[i]["bench_pd"].add_child_pd(pd)
            core_objs[i]["children"].append((child_id, pd.name))

        core_objs[i]["init_ch"] = Channel(core_objs[i]["idle_pd"], core_objs[i]["bench_pd"])
        sdf.add_channel(core_objs[i]["init_ch"])

        if i == 0:
            core_objs[i]["start_ch"] = Channel(bench_client_pd, core_objs[i]["bench_pd"])
            core_objs[i]["stop_ch"] = Channel(bench_client_pd, core_objs[i]["bench_pd"])
        else:
            core_objs[i]["start_ch"] = Channel(core_objs[i - 1]["bench_pd"], core_objs[i]["bench_pd"])
            core_objs[i]["stop_ch"] = Channel(core_objs[i - 1]["bench_pd"], core_objs[i]["bench_pd"])
        sdf.add_channel(core_objs[i]["start_ch"])
        sdf.add_channel(core_objs[i]["stop_ch"])

        cycle_counters_mr = MemoryRegion(sdf, f"cycle_counters{core}", 0x1000)
        sdf.add_mr(cycle_counters_mr)
        core_objs[i]["idle_pd"].add_map(Map(cycle_counters_mr, 0x5_000_000, perms="rw"))
        bench_client_pd.add_map(Map(cycle_counters_mr, 0x20_000_000 + 0x1000 * i, perms="r"))

        core_objs[i]["idle_config"] = BenchmarkIdleConfig(
            0x5_000_000, core_objs[i]["init_ch"].pd_a_id
        )
        if i == 0:
            bench_client_config = BenchmarkClientConfig(
                core_objs[i]["start_ch"].pd_a_id,
                core_objs[i]["stop_ch"].pd_a_id,
                [0x20_000_000 + 0x1000 * j for j in range(num_cores)],
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
                core_objs[i - 1]["children"],
                list(pmu_event_ids),
            )
    core_objs[num_cores - 1]["bench_config"] = BenchmarkConfig(
        core_objs[num_cores - 1]["start_ch"].pd_b_id,
        0,
        core_objs[num_cores - 1]["stop_ch"].pd_b_id,
        0,
        core_objs[num_cores - 1]["init_ch"].pd_b_id,
        core_objs[num_cores - 1]["core"],
        True,
        core_objs[num_cores - 1]["children"],
        list(pmu_event_ids),
    )

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert net_system.connect()
    assert net_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)
    for c in clients:
        assert c["lwip"].connect()
        assert c["lwip"].serialise_config(output_dir)

    # Per-client section injection (one copied ELF each).
    for c in clients:
        i = c["i"]
        update_elf_section(c["elf"], "timer_client_config", f"timer_client_client{i}")
        update_elf_section(c["elf"], "net_client_config", f"net_client_client{i}")
        update_elf_section(c["elf"], "serial_client_config", f"serial_client_client{i}")
        update_elf_section(c["elf"], "lib_sddf_lwip_config", f"lib_sddf_lwip_config_client{i}")
        update_elf_section(c["copier_elf"], "net_copy_config", f"net_copy_client{i}_net_copier")

        app_config = IperfAppConfig(i)
        with open(f"{output_dir}/iperf3_app_config{i}.data", "wb+") as f:
            f.write(app_config.serialise())
        update_elf_section(c["elf"], "iperf3_app_config", "iperf3_app_config", i)

        with open(f"{output_dir}/iperf3_multi_config{i}.data", "wb+") as f:
            f.write(multi_cfg_by_i[i].serialise())
        update_elf_section(c["elf"], "iperf3_multi_config", "iperf3_multi_config", i)

    # Benchmark client config goes to client0 only.
    with open(f"{output_dir}/benchmark_client_config.data", "wb+") as f:
        f.write(bench_client_config.serialise())
    update_elf_section(clients[0]["elf"], "benchmark_client_config", "benchmark_client_config")

    # Per-core benchmark + idle configs.
    for i in range(num_cores):
        core = core_objs[i]["core"]
        update_elf_section(core_objs[i]["bench_elf"], "serial_client_config", "serial_client_bench", core)
        with open(f"{output_dir}/benchmark_config{core}.data", "wb+") as f:
            f.write(core_objs[i]["bench_config"].serialise())
        update_elf_section(core_objs[i]["bench_elf"], "benchmark_config", "benchmark_config", core)
        with open(f"{output_dir}/benchmark_idle_config{core}.data", "wb+") as f:
            f.write(core_objs[i]["idle_config"].serialise())
        update_elf_section(core_objs[i]["idle_elf"], "benchmark_config", "benchmark_idle_config", core)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


bench_pmu_events = {
    "CACHE_L1I_MISS": (0, []),
    "CACHE_L1D_MISS": (1, []),
    "TLB_L1I_MISS": (2, []),
    "TLB_L1D_MISS": (3, []),
    "EXECUTE_INSTRUCTION": (4, []),
    "BRANCH_MISPREDICT": (5, []),
    "CPU_CYCLES": (6, []),
    "MEM_ACCESS": (7, []),
    "CHAIN": (8, []),
}


def resolve_pmu_events(events: List[str], board: str) -> List[int]:
    """Map PMU event names to their enum ids, validating as we go."""

    ids = []
    for i, event in enumerate(events):
        ids.append(bench_pmu_events[event][0])

    return ids


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--objcopy", required=True)
    parser.add_argument("--smp", required=True)
    parser.add_argument("--bench_pmu_events", required=False)
    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    global obj_copy
    obj_copy = args.objcopy

    with open(args.smp, "r") as core_alloc:
        core_dict = json.load(core_alloc)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    if args.bench_pmu_events:
        pmu_events = args.bench_pmu_events.split(",")
    else:
        # If benchmarking PMU events are not provided, we use these default events
        pmu_events = [
            "EXECUTE_INSTRUCTION",
            "CHAIN",
            "MEM_ACCESS",
            "CHAIN",
            "CACHE_L1D_MISS",
            "CHAIN",
        ]

    pmu_event_ids = resolve_pmu_events(pmu_events, args.board)

    generate(args.sdf, args.output, dtb, core_dict, pmu_event_ids)
