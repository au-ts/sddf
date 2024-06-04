#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/util/cache.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#define DRIVER 0
#define CLIENT_CH 1

net_queue_t *tx_free_drv;
net_queue_t *tx_active_drv;
net_queue_t *tx_free_cli0;
net_queue_t *tx_active_cli0;

uintptr_t buffer_data_region_cli0_vaddr;
uintptr_t buffer_data_region_cli0_paddr;
uintptr_t buffer_data_region_cli1_paddr;

net_queue_handle_t *tx_queue_drv;
net_queue_handle_t *tx_queue_clients;

uintptr_t *buffer_region_vaddrs;
uintptr_t *buffer_region_paddrs;

static char cml_memory[1280];

extern void cml_main(void);
extern void notified(microkit_channel ch);
extern void tx_provide(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

void cml_exit(int arg) {
    microkit_dbg_puts("ERROR! We should not be getting here\n");
}

void cml_err(int arg) {
    if (arg == 3) {
        microkit_dbg_puts("Memory not ready for entry. You may have not run the init code yet, or be trying to enter during an FFI call.\n");
    }
  cml_exit(arg);
}

// Need to come up with a replacement for this clear cache function. Might be worth testing just flushing the entire l1 cache, but might cause issues with returning to this file
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
    uintptr_t *heap = (uintptr_t *) cml_heap;
    tx_queue_drv = (net_queue_handle_t *) &heap[0];
    buffer_region_vaddrs = (uintptr_t *) &heap[3];
    buffer_region_paddrs =  (uintptr_t *) &heap[5];
    tx_queue_clients = (net_queue_handle_t *) &heap[7];
}

void init(void)
{
    init_pancake_mem();
    init_pancake_data();

    net_queue_init(tx_queue_drv, tx_free_drv, tx_active_drv, NET_TX_QUEUE_SIZE_DRIV);
    net_virt_queue_init_sys(microkit_name, tx_queue_clients, tx_free_cli0, tx_active_cli0);

    net_mem_region_init_sys(microkit_name, buffer_region_vaddrs, buffer_data_region_cli0_vaddr);

    /* CDTODO: Can we make this system agnostic? */
    buffer_region_paddrs[0] = buffer_data_region_cli0_paddr;
    buffer_region_paddrs[1] = buffer_data_region_cli1_paddr;

    cml_main();

    tx_provide();
}
