import argparse
import struct
from sdfgen import SystemDescription, Sddf, DeviceTree
ProtectionDomain = SystemDescription.ProtectionDomain

PLATFORMS = [
    {
        "name": "qemu_virt_aarch64",
        "arch": SystemDescription.Arch.AARCH64,
        "paddr_top": 0xa_000_000,
        "timer_device_node": "timer",
        "uart_device_node": "pl011@9000000",
        "ethernet_device_node": "virtio_mmio@a003e00",
    },
    {
        "name": "odroidc4",
        "arch": SystemDescription.Arch.AARCH64,
        "paddr_top": 0x80000000,
        "timer_device_node": "soc/bus@ffd00000/watchdog@f0d0",
        "uart_device_node": "soc/bus@ff800000/serial@3000",
        "ethernet_device_node": "soc/ethernet@ff3f0000",
    },
    {
        "name": "maaxboard",
        "arch": SystemDescription.Arch.AARCH64,
        "paddr_top": 0xa0000000,
        "timer_device_node": "soc@0/bus@30000000/timer@302d0000",
        "uart_device_node": "soc@0/bus@30800000/serial@30860000",
        "ethernet_device_node": "soc@0/bus@30800000/ethernet@30be0000",
    },
]

# Classes to serialise into custom configuration for the benchmarking
# component.
# All serialised definitions are little endian and pointers are 64-bit
# integers.

class BenchmarkIdleConfig:
    def __init__(self, cycle_counters, ch_init):
        self.cycle_counters = cycle_counters
        self.ch_init = ch_init

    '''
        Matches struct definition:
        {
            void *;
            uint8_t;
        }

        Little endian. Pointers are 64-bit integers.
    '''
    def serialise(self) -> bytes:
        struct.pack(">qc", self.cycle_counters, self.ch_init)


class BenchmarkClientConfig:
    def __init__(self, cycle_counters, ch_start, ch_stop):
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
        return struct.pack(">qcc", self.cycle_counters, self.ch_start, self.ch_stop)


# class BenchmarkConfig:
#     def __init__(self, ch_start, ch_stop, ch_init, children):
#         self.ch_start = ch_start
#         self.ch_stop = ch_stop
#         self.ch_init = ch_init
#         self.children = children


#     def serialise(self) -> bytes:



def generate_sdf(output: str):
    uart_node = dtb.node(platform["uart_device_node"])
    assert uart_node is not None
    ethernet_node = dtb.node(platform["ethernet_device_node"])
    assert ethernet_node is not None
    timer_node = dtb.node(platform["timer_device_node"])
    assert uart_node is not None

    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf")
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)

    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=199)
    serial_virt_rx = ProtectionDomain("serial_virt_rx", "serial_virt_rx.elf", priority=199)
    serial_system = Sddf.Serial(sdf, uart_node, serial_driver, serial_virt_tx, serial_virt_rx)

    ethernet_driver = ProtectionDomain("ethernet_driver", "ethernet_driver.elf")
    net_virt_tx = ProtectionDomain("net_virt_tx", "net_virt_tx.elf")
    net_virt_rx = ProtectionDomain("net_virt_tx", "net_virt_tx.elf")
    net_system = Sddf.Network(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)

    client = ProtectionDomain("client", "lwip.elf", priority=1)
    client_net_copier = ProtectionDomain("client_net_copier", "client_net_copier.elf", priority=1)

    serial_system.add_client(client)
    timer_system.add_client(client)
    net_system.add_client_with_copier(client, client_net_copier, mac_addr="0f:1f:2f:3f:4f:5f")

    # Benchmark specific resources

    bench_idle = ProtectionDomain("bench_idle", "idle.elf")
    bench = ProtectionDomain("bench", "benchmark.elf")

    benchmark_pds = [
        serial_driver,
        serial_virt_tx,
        serial_virt_rx,
        ethernet_driver,
        net_virt_tx,
        net_virt_rx,
        client,
        client_net_copier,
    ]
    pds = [
        bench_idle,
        bench,
    ]
    for pd in benchmark_pds:
        print(bench.add_child_pd(pd))
    for pd in pds:
        sdf.add_pd(pd)

    # Connect everything up together
    serial_system.connect()
    net_system.connect()
    timer_system.connect()


    with open(output + "echo_server.system", "w+") as f:
        f.write(sdf.xml())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtbs", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--platform", required=True, choices=[p["name"] for p in PLATFORMS])
    parser.add_argument("--output", required=True)

    args = parser.parse_args()

    platform = next(filter(lambda p: p["name"] == args.platform, PLATFORMS))
    platform_name = platform["name"]

    sdf = SystemDescription(platform["arch"], platform["paddr_top"])
    sddf = Sddf(args.sddf)

    with open(args.dtbs + f"/{platform_name}.dtb", "rb") as f:
        dtb = DeviceTree(f.read())

    generate_sdf(args.output)
