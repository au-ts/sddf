#include <string.h>
#include <stdbool.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#define VIRT_RX_CH 0
#define CLIENT_CH 1

uintptr_t rx_free_virt;
uintptr_t rx_active_virt;
uintptr_t rx_free_cli;
uintptr_t rx_active_cli;

uintptr_t virt_buffer_data_region;
uintptr_t cli_buffer_data_region;

net_queue_handle_t *rx_queue_virt;
net_queue_handle_t *rx_queue_cli;

static char cml_memory[1280];
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

extern void cml_main(void);
extern void notified(microkit_channel ch);

void cml_exit(int arg) {
    microkit_dbg_puts("ERROR! We should not be getting here\n");
}

void cml_err(int arg) {
    if (arg == 3) {
        microkit_dbg_puts("Memory not ready for entry. You may have not run the init code yet, or be trying to enter during an FFI call.\n");
    }
  cml_exit(arg);
}

/* Need to come up with a replacement for this clear cache function. Might be worth testing just flushing the entire l1 cache, but might cause issues with returning to this file*/
void cml_clear() {
    microkit_dbg_puts("Trying to clear cache\n");
}

void init_pancake_mem() {
    unsigned long cml_heap_sz = 256;
    unsigned long cml_stack_sz = 1024;
    cml_heap = cml_memory;
    cml_stack = cml_heap + cml_heap_sz;
    cml_stackend = cml_stack + cml_stack_sz;
}

void init_pancake_data() {
    uintptr_t *heap = (uintptr_t *)cml_heap;
    heap[0] = virt_buffer_data_region;
    heap[1] = cli_buffer_data_region;
    rx_queue_virt = (net_queue_handle_t *) &heap[2];
    rx_queue_cli = (net_queue_handle_t *) &heap[5];
}

void init(void)
{
    init_pancake_mem();
    init_pancake_data();
    net_copy_queue_init_sys(microkit_name, rx_queue_cli, rx_free_cli, rx_active_cli, rx_queue_virt, rx_free_virt,
                            rx_active_virt);
    net_buffers_init(rx_queue_cli, 0);
    cml_main();
}
