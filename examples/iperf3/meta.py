import sys, os
import argparse
import struct
import json
import subprocess
import shutil
from typing import List, Tuple, Callable
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)
from board import BOARDS

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel


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
    ):
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
            c_name_padded = c_name.ljust(64, b"\0")
            assert len(c_name_padded) == 64
            child_bytes.extend(c_name_padded)
            child_bytes.extend(child[0].to_bytes(1, "little"))
        child_bytes = child_bytes.ljust(64 * 65, b"\0")
        child_bytes_list = [x.to_bytes(1, "little") for x in child_bytes]
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
        )


def generate(
  sdf_file: str, output_dir: str, dtb: DeviceTree, get_core: Callable[[str],int]
):
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
        "serial_driver",
        "serial_driver.elf",
        priority=100,
        cpu=get_core("serial_driver"),
    )

    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx",
        "serial_virt_tx.elf",
        priority=99,
        cpu=get_core("serial_virt_tx"),
    )
    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx)
    
    ethernet_driver = ProtectionDomain(
        "ethernet_driver",
        "eth_driver.elf",
        priority=101,
        budget=100,
        period=400,
        cpu=get_core("ethernet_driver"),
    )
    
    if board.name == "star64":
        # For ethernet reset, the Pine64 Star64 driver needs access to the
        # clock controller. We do not have a clock driver for this platform so the
        # ethernet driver does it directly.
        clock_controller = MemoryRegion(
        sdf, "clock_controller", 0x10_000, paddr=0x17000000
        )
        sdf.add_mr(clock_controller)
        ethernet_driver.add_map(Map(clock_controller, 0x3000000, perms="rw"))
    
    net_virt_tx = ProtectionDomain(
        "net_virt_tx",
        "network_virt_tx.elf",
        priority=100,
        budget=20000,
        cpu=get_core("net_virt_tx"),
    )
    
    net_virt_rx = ProtectionDomain(
        "net_virt_rx", "network_virt_rx.elf", priority=99, cpu=get_core("net_virt_rx")
    )
    
    net_system = Sddf.Net(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)
    
    iperf_elf = "iperf3_client.elf"
    iperf = ProtectionDomain(
        "iperf3", iperf_elf, priority=98, budget=20000, cpu=get_core("iperf3"), stack_size=0x1000000
    )
    
    iperf_net_copier_elf = "network_copy.elf"
    iperf_net_copier = ProtectionDomain(
        "iperf_net_copier",
        iperf_net_copier_elf,
        priority=97,
        cpu=get_core("iperf3_net_copier"),
    )
    # Benchmark infrastructure: idle PD (priority 1) spins reading the cycle
    # counter and writes core_ccount/idle_ccount to shared memory.  The
    # benchmark PD (priority 254) initialises the idle PD and handles
    # START/STOP notifications from the iperf3 client.
    bench_core = get_core("iperf3")  # measure the same core as iperf3
    idle_pd = ProtectionDomain(
        "bench_idle", "idle.elf", priority=1, cpu=bench_core
    )
    bench_pd = ProtectionDomain(
        "benchmark", "benchmark.elf", priority=254, cpu=bench_core
    )

    # Channels
    init_ch = Channel(idle_pd, bench_pd)       # bench_pd notifies idle_pd to start spinning
    start_ch = Channel(iperf, bench_pd)        # iperf3 client notifies benchmark PD on test start
    stop_ch = Channel(iperf, bench_pd)         # iperf3 client notifies benchmark PD on test stop

    sdf.add_channel(init_ch)
    sdf.add_channel(start_ch)
    sdf.add_channel(stop_ch)

    # Shared memory: idle PD writes counters here; iperf3 client reads them
    cycle_counters_mr = MemoryRegion(sdf, "cycle_counters", 0x1000)
    sdf.add_mr(cycle_counters_mr)
    idle_pd.add_map(Map(cycle_counters_mr, 0x5_000_000, perms="rw"))
    iperf.add_map(Map(cycle_counters_mr, 0x20_000_000, perms="r"))

    sdf.add_pd(iperf_net_copier)
    sdf.add_pd(iperf)
    sdf.add_pd(net_virt_rx)
    sdf.add_pd(net_virt_tx)
    sdf.add_pd(ethernet_driver)
    sdf.add_pd(serial_virt_tx)
    sdf.add_pd(timer_driver)
    sdf.add_pd(uart_driver)
    sdf.add_pd(idle_pd)
    sdf.add_pd(bench_pd)

    serial_system.add_client(iperf)
    serial_system.add_client(bench_pd)
    timer_system.add_client(iperf)

    net_system.add_client_with_copier(iperf, iperf_net_copier)

    iperf_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, iperf)

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)

    assert net_system.connect()
    assert net_system.serialise_config(output_dir)

    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

    assert iperf_lib_sddf_lwip.connect()
    assert iperf_lib_sddf_lwip.serialise_config(output_dir)

    # Serialise benchmark configs
    bench_client_config = BenchmarkClientConfig(
        start_ch.pd_a_id,
        stop_ch.pd_a_id,
        [0x20_000_000],  # one core, mapped at this vaddr in iperf3 client
    )
    idle_config = BenchmarkIdleConfig(0x5_000_000, init_ch.pd_a_id)
    bench_config = BenchmarkConfig(
        ch_rx_start=start_ch.pd_b_id,
        ch_tx_start=0,
        ch_rx_stop=stop_ch.pd_b_id,
        ch_tx_stop=0,
        ch_init=init_ch.pd_b_id,
        core=bench_core,
        last_core=True,
        children=[],
    )

    with open(f"{output_dir}/benchmark_client_config.data", "wb+") as f:
        f.write(bench_client_config.serialise())

    with open(f"{output_dir}/benchmark_config.data", "wb+") as f:
        f.write(bench_config.serialise())

    with open(f"{output_dir}/benchmark_idle_config.data", "wb+") as f:
        f.write(idle_config.serialise())

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())
        
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--objcopy", required=True)
    parser.add_argument("--smp", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    global obj_copy
    obj_copy = args.objcopy

    with open(args.smp, "r") as core_alloc:
        core_dict = json.load(core_alloc)
    get_core = lambda name: core_dict[name]

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb, get_core)

    
  
 