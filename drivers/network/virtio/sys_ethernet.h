#include "ethernet.h"

#ifdef MICROKIT
#include <microkit.h>
#include <ethernet_config.h>

#define IRQ_CH 0
#define TX_CH  1
#define RX_CH  2

uintptr_t eth_regs;
/*
 * The 'hardware' ring buffer region is used to store the virtIO virtqs
 * as well as the RX and TX virtIO headers.
 */
uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;

net_queue_t *rx_free;
net_queue_t *rx_active;
net_queue_t *tx_free;
net_queue_t *tx_active;

void init(void) {
    resources = (struct resources) {
        .regs = eth_regs,
        .hw_ring_buffer_vaddr = hw_ring_buffer_vaddr,
        .hw_ring_buffer_paddr = hw_ring_buffer_paddr,
        .rx_free = rx_free,
        .rx_active = rx_active,
        .tx_free = tx_free,
        .tx_active = tx_active,
        .rx_queue_size = NET_RX_QUEUE_SIZE_DRIV,
        .tx_queue_size = NET_TX_QUEUE_SIZE_DRIV,

        .irq_id = IRQ_CH,
        .rx_id = RX_CH,
        .tx_id = TX_CH,
    };

    sddf_init();
}

void notified(microkit_channel ch) {
	sddf_notified(ch);
}

static inline void sddf_irq_ack(microkit_channel ch) {
	microkit_irq_ack(ch);
}

static inline void sddf_notify(microkit_channel ch) {
	microkit_notify(ch);
}

#else

#include <sel4/sel4.h>

extern inline void sddf_irq_ack(unsigned int id);
extern inline void sddf_notify(unsigned int id);

#endif /* MICROKIT */