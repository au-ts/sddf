const std = @import("std");
const sdfgen = @import("sdf");
const dtb = sdfgen.dtb;

const sddf = sdfgen.sddf;
const Allocator = std.mem.Allocator;
const SystemDescription = sdfgen.sdf.SystemDescription;
const Pd = SystemDescription.ProtectionDomain;

const blob_bytes = @embedFile("qemu_virt_aarch64.dtb");

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const allocator = arena.allocator();
    defer arena.deinit();

    try sddf.probe(allocator, "../../");

    var blob = try dtb.parse(allocator, blob_bytes);
    defer blob.deinit(allocator);

    var sdf = SystemDescription.create(allocator, .aarch64, 0xa0000000);

    const uart_node = blob.child("pl011@9000000").?;

    var uart_driver = Pd.create(allocator, "uart_driver", "uart_driver.elf");
    sdf.addProtectionDomain(&uart_driver);

    var serial_virt_rx = Pd.create(allocator, "serial_virt_rx", "serial_virt_rx.elf");
    sdf.addProtectionDomain(&serial_virt_rx);
    var serial_virt_tx = Pd.create(allocator, "serial_virt_tx", "serial_virt_tx.elf");
    sdf.addProtectionDomain(&serial_virt_tx);

    var client0 = Pd.create(allocator, "client0", "serial_server.elf");
    sdf.addProtectionDomain(&client0);
    var client1 = Pd.create(allocator, "client1", "serial_server.elf");
    sdf.addProtectionDomain(&client1);
    var client2 = Pd.create(allocator, "client2", "serial_server.elf");
    sdf.addProtectionDomain(&client2);

    var serial_system = try sddf.SerialSystem.init(allocator, &sdf, uart_node, &uart_driver, &serial_virt_tx, &serial_virt_rx, .{ .rx = true });
    serial_system.addClient(&client0);
    serial_system.addClient(&client1);
    serial_system.addClient(&client2);

    uart_driver.priority = 100;
    serial_virt_tx.priority = 99;
    serial_virt_rx.priority = 98;

    try serial_system.connect();
    try serial_system.serialiseConfig();
    try sdf.print();
}
