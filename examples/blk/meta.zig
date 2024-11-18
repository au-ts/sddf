const std = @import("std");
const sdfgen = @import("sdf");
const dtb = sdfgen.dtb;
const config = @import("config");

const sddf = sdfgen.sddf;
const Allocator = std.mem.Allocator;
const SystemDescription = sdfgen.sdf.SystemDescription;
const Pd = SystemDescription.ProtectionDomain;

const blob_bytes = @embedFile("qemu_virt_aarch64.dtb");

fn fmt(allocator: Allocator, comptime s: []const u8, args: anytype) []u8 {
    return std.fmt.allocPrint(allocator, s, args) catch @panic("OOM");
}

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const allocator = arena.allocator();
    defer arena.deinit();

    try sddf.probe(allocator, "../../");

    var blob = try dtb.parse(allocator, blob_bytes);
    defer blob.deinit(allocator);

    var sdf = SystemDescription.create(allocator, .aarch64, 0xa0000000);

    const blk_node = blob.child("virtio_mmio@a003e00").?;

    var blk_driver = Pd.create(allocator, "blk_driver", "blk_driver.elf");
    sdf.addProtectionDomain(&blk_driver);
    var blk_virt = Pd.create(allocator, "blk_virt", "blk_virt.elf");
    sdf.addProtectionDomain(&blk_virt);

    var blk_system = sddf.BlockSystem.init(allocator, &sdf, blk_node, &blk_driver, &blk_virt, .{});


    for (0..config.num_clients) |i| {
        const client = try allocator.create(Pd);
        client.* = Pd.create(allocator, fmt(allocator, "client{}", .{ i }), "client.elf");
        sdf.addProtectionDomain(client);
        blk_system.addClient(client);
    }

    _ = try blk_system.connect();

    try blk_system.serialiseConfig("blk_virt.data");

    try sdf.print();
}
