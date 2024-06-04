#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/network/constants.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/util/cache.h>
#include <ethernet_config.h>

/* Notification channels */
#define DRIVER_CH 0
#define CLIENT_CH 1

/* Used to signify that a packet has come in for the broadcast address and does not match with
 * any particular client. */
#define BROADCAST_ID (NUM_NETWORK_CLIENTS + 1)

/* Queue regions */
net_queue_t *rx_free_drv;
net_queue_t *rx_active_drv;
net_queue_t *rx_free_cli0;
net_queue_t *rx_active_cli0;

/* Buffer data regions */
uintptr_t buffer_data_vaddr;
uintptr_t buffer_data_paddr;

/* In order to handle broadcast packets where the same buffer is given to multiple clients
  * we keep track of a reference count of each buffer and only hand it back to the driver once
  * all clients have returned the buffer. */
uint64_t *buffer_refs;

net_queue_handle_t *rx_queue_drv;
net_queue_handle_t *rx_queue_clients;

uint8_t *mac_addrs;

static char cml_memory[1024*2];

extern void cml_main(void);
extern void notified(microkit_channel ch);
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
    unsigned long cml_heap_sz = 1024;
    unsigned long cml_stack_sz = 1024;
    cml_heap = cml_memory;
    cml_stack = cml_heap + cml_heap_sz;
    cml_stackend = cml_stack + cml_stack_sz;
}

void init_pancake_data() {
    uintptr_t *heap = (uintptr_t *) cml_heap;
    // notify_drv = (uint64_t *) &heap[0];
    rx_queue_drv = (net_queue_handle_t *) &heap[1];
    heap[4] = buffer_data_vaddr;
    heap[5] = buffer_data_paddr;
    rx_queue_clients = (net_queue_handle_t *) &heap[6];
    int offset = sizeof(net_queue_handle_t) * NUM_NETWORK_CLIENTS;
    mac_addrs = (uint8_t *) ((char *) &heap[6] + offset);
}

void init(void)
{
    init_pancake_mem();
    init_pancake_data();

    net_virt_mac_addr_init_sys(microkit_name, (uint8_t *) mac_addrs);

    net_queue_init(rx_queue_drv, rx_free_drv, rx_active_drv, NET_RX_QUEUE_SIZE_DRIV);
    net_virt_queue_init_sys(microkit_name, rx_queue_clients, rx_free_cli0, rx_active_cli0);
    net_buffers_init(rx_queue_drv, buffer_data_paddr);

    if (net_require_signal_free(rx_queue_drv)) {
        net_cancel_signal_free(rx_queue_drv);
        microkit_deferred_notify(DRIVER_CH);
    }

    cml_main();
}
