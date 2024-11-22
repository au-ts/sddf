import argparse
from sdfgen import SystemDescription, ProtectionDomain, Sddf, DeviceTree, LionsOS, Channel

PLATFORMS = [
    {
        "name": "qemu_virt_aarch64",
        "arch": 1,
        "paddr_top": 0xa_000_000,
        "timer_device_node": "timer",
    },
    {
        "name": "odroidc4",
        "arch": 1,
        "paddr_top": 0x80000000,
        "timer_device_node": "soc/bus@ffd00000/watchdog@f0d0",
    },
    {
        "name": "star64",
        "arch": 3,
        "paddr_top": 0x100000000,
        "timer_device_node": "soc/timer@13050000",
    },
]

def generate_sdf():
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=200)
    client = ProtectionDomain("client", "client.elf", priority=1)

    timer_node = dtb.node(platform["timer_device_node"])
    assert timer_node is not None

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)

    pds = [
        timer_driver,
        client
    ]
    for pd in pds:
        sdf.add_pd(pd)

    timer_system.connect()

    print(sdf.xml())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtbs", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--platform", required=True, choices=[p["name"] for p in PLATFORMS])

    args = parser.parse_args()

    platform = next(filter(lambda p: p["name"] == args.platform, PLATFORMS))
    platform_name = platform["name"]

    sdf = SystemDescription(platform["arch"], platform["paddr_top"])
    sddf = Sddf(args.sddf)

    with open(args.dtbs + f"/{platform_name}.dtb", "rb") as f:
        dtb = DeviceTree(f.read())

    generate_sdf()
