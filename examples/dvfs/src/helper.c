#include <sddf/timer/config.h>
#include <sddf/timer/client.h>
#include <sddf/serial/config.h>
#include <sddf/serial/queue.h>
#include <sddf/util/printf.h>
#include <sddf/benchmark/sel4bench.h>

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

serial_queue_handle_t serial_tx_queue_handle;

void wait() {
    sddf_timer_set_timeout(timer_config.driver_id, 1000000000);
}

void print_count(uint64_t cycle) {
    sddf_printf("Cycle count: %lu\n", cycle);
}

uint64_t read_count() {
    uint64_t ccnt;
    SEL4BENCH_READ_CCNT(ccnt);
    return ccnt;
}

void counter_init() {
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);
    sel4bench_init();
}
