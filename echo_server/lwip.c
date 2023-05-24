/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <sel4cp.h>
#include <string.h>
#include "lwip/init.h"
#include "netif/etharp.h"
#include "lwip/pbuf.h"
#include "lwip/netif.h"
#include "lwip/stats.h"
#include "lwip/snmp.h"
#include "lwip/sys.h"
#include "lwip/dhcp.h"

#include "shared_ringbuffer.h"
#include "echo.h"
#include "timer.h"

#define IRQ    1
#define RX_CH  2
#define TX_CH  3
#define INIT   6

#define LINK_SPEED 1000000000 // Gigabit
#define ETHER_MTU 1500
#define NUM_BUFFERS 512
#define BUF_SIZE 2048

/* Memory regions. These all have to be here to keep compiler happy */
uintptr_t rx_free;
uintptr_t rx_used;
uintptr_t tx_free;
uintptr_t tx_used;
uintptr_t shared_dma_vaddr_rx;
uintptr_t shared_dma_vaddr_tx;
uintptr_t uart_base;

static bool notify_tx = false;

typedef enum {
    ORIGIN_RX_QUEUE,
    ORIGIN_TX_QUEUE,
} ethernet_buffer_origin_t;

typedef struct ethernet_buffer {
    /* The acutal underlying memory of the buffer */
    uintptr_t buffer;
    /* The physical size of the buffer */
    size_t size;
    /* Queue from which the buffer was allocated */
    char origin;
    /* Index into buffer_metadata array */
    unsigned int index;
    /* in use */
    bool in_use;
} ethernet_buffer_t;

typedef struct state {
    struct netif netif;
    /* mac address for this client */
    uint8_t mac[6];

    /* Pointers to shared buffers */
    ring_handle_t rx_ring;
    ring_handle_t tx_ring;
    /*
     * Metadata associated with buffers
     */
    ethernet_buffer_t buffer_metadata[NUM_BUFFERS * 2];
} state_t;

state_t state;

/* 
 * LWIP mempool declare literally just initialises an array 
 * big enough with the correct alignment 
 */
typedef struct lwip_custom_pbuf {
    struct pbuf_custom custom;
    ethernet_buffer_t *buffer;
} lwip_custom_pbuf_t;
LWIP_MEMPOOL_DECLARE(
    RX_POOL,
    NUM_BUFFERS * 2,
    sizeof(lwip_custom_pbuf_t),
    "Zero-copy RX pool"
);

static void
dump_mac(uint8_t *mac)
{
    sel4cp_dbg_puts("Lwip MAC: ");
    for (unsigned i = 0; i < 6; i++) {
        sel4cp_dbg_putc(hexchar((mac[i] >> 4) & 0xf));
        sel4cp_dbg_putc(hexchar(mac[i] & 0xf));
        if (i < 5) {
            sel4cp_dbg_putc(':');
        }
    }
    sel4cp_dbg_putc('\n');
}

static bool notify_rx = false;

static inline void return_buffer(ethernet_buffer_t *buffer)
{
    /* As the rx_free ring is the size of the number of buffers we have,
    the ring should never be full. 
    FIXME: This full condition could change... */
    bool was_empty = ring_empty(state.rx_ring.free_ring);
    int err = enqueue_free(&(state.rx_ring), buffer->buffer, BUF_SIZE, buffer);
    assert(!err);
    if (was_empty) {
        notify_rx = true;
    }
}

/**
 * Free a pbuf. This also returns the underlying buffer to
 * the appropriate place.
 *
 * @param buf pbuf to free.
 *
 */
static void interface_free_buffer(struct pbuf *buf)
{
    SYS_ARCH_DECL_PROTECT(old_level);

    lwip_custom_pbuf_t *custom_pbuf = (lwip_custom_pbuf_t *) buf;

    SYS_ARCH_PROTECT(old_level);
    return_buffer(custom_pbuf->buffer);
    LWIP_MEMPOOL_FREE(RX_POOL, custom_pbuf);
    SYS_ARCH_UNPROTECT(old_level);
}

/**
 * Create a pbuf structure to pass to the network interface.
 *
 * @param state client state data.
 * @param buffer ethernet buffer containing metadata for the actual buffer
 * @param length length of data
 *
 * @return the newly created pbuf.
 */
static struct pbuf *create_interface_buffer(state_t *state, ethernet_buffer_t *buffer, size_t length)
{
    lwip_custom_pbuf_t *custom_pbuf = (lwip_custom_pbuf_t *) LWIP_MEMPOOL_ALLOC(RX_POOL);

    // custom_pbuf->state = state;
    custom_pbuf->buffer = buffer;
    custom_pbuf->custom.custom_free_function = interface_free_buffer;

    return pbuf_alloced_custom(
        PBUF_RAW,
        length,
        PBUF_REF,
        &custom_pbuf->custom,
        (void *)buffer->buffer,
        buffer->size
    );
}

/**
 * Allocate an empty TX buffer from the empty pool
 *
 * @param state client state data.
 * @param length length of buffer required
 *
 */
static inline ethernet_buffer_t *alloc_tx_buffer(size_t length)
{
    if (BUF_SIZE < length) {
        sel4cp_dbg_puts("Requested buffer size too large.");
        return NULL;
    }

    uintptr_t addr;
    unsigned int len;
    ethernet_buffer_t *buffer;

    int err = dequeue_free(&(state.tx_ring), &addr, &len, (void **)&buffer);
    if (err) {
        print("LWIP|ERROR: TX free ring is empty!\n");
        return NULL;
    }

    if (!buffer) {
        print("LWIP|ERROR: dequeued a null ethernet buffer\n");
        return NULL;
    }

    if (addr != buffer->buffer) {
        print("LWIP|ERROR: sanity check failed\n");
    }

    return buffer;
}

static err_t lwip_eth_send(struct netif *netif, struct pbuf *p)
{
    /* Grab an free TX buffer, copy pbuf data over,
    add to used tx ring, notify server */
    err_t ret = ERR_OK;

    if (p->tot_len > BUF_SIZE) {
        print("LWIP|ERROR: lwip_eth_send total length > BUF SIZE\n");
        return ERR_MEM;
    }

    ethernet_buffer_t *buffer = alloc_tx_buffer(p->tot_len);
    if (buffer == NULL) {
        return ERR_MEM;
    }
    unsigned char *frame = (unsigned char *)buffer->buffer;

    /* Copy all buffers that need to be copied */
    unsigned int copied = 0;
    for (struct pbuf *curr = p; curr != NULL; curr = curr->next) {
        unsigned char *buffer_dest = &frame[copied];
        if ((uintptr_t)buffer_dest != (uintptr_t)curr->payload) {
            /* Don't copy memory back into the same location */
            memcpy(buffer_dest, curr->payload, curr->len);
        }
        copied += curr->len;
    }

    int err = seL4_ARM_VSpace_Clean_Data(3, (uintptr_t)frame, (uintptr_t)frame + copied);
    if (err) {
        print("LWIP|ERROR: ARM VSpace clean failed: ");
        puthex64(err);
        print("\n");
    }

    /* insert into the used tx queue */
    err = enqueue_used(&(state.tx_ring), (uintptr_t)frame, copied, buffer);
    if (err) {
        print("LWIP|ERROR: TX used ring full\n");
        err = enqueue_free(&(state.tx_ring), (uintptr_t)frame, BUF_SIZE, buffer);
        assert(!err);
        return ERR_MEM;
    }

    /* Notify the server for next time we recv() */
    notify_tx = true;
    return ret;
}

void process_rx_queue(void)
{
    while (!ring_empty(state.rx_ring.used_ring) && !ring_empty(state.tx_ring.free_ring)) {
        uintptr_t addr;
        unsigned int len;
        ethernet_buffer_t *buffer;

        dequeue_used(&state.rx_ring, &addr, &len, (void **)&buffer);

        if (addr != buffer->buffer) {
            print("LWIP|ERROR: sanity check failed\n");
        }

        struct pbuf *p = create_interface_buffer(&state, (void *)buffer, len);

        if (state.netif.input(p, &state.netif) != ERR_OK) {
            // If it is successfully received, the receiver controls whether or not it gets freed.
            print("LWIP|ERROR: netif.input() != ERR_OK");
            pbuf_free(p);
        }
    }
}

/**
 * Initialise the network interface data structure.
 *
 * @param netif network interface data structuer.
 */
static err_t ethernet_init(struct netif *netif)
{
    if (netif->state == NULL) {
        return ERR_ARG;
    }

    state_t *data = netif->state;

    netif->hwaddr[0] = data->mac[0];
    netif->hwaddr[1] = data->mac[1];
    netif->hwaddr[2] = data->mac[2];
    netif->hwaddr[3] = data->mac[3];
    netif->hwaddr[4] = data->mac[4];
    netif->hwaddr[5] = data->mac[5];
    netif->mtu = ETHER_MTU;
    netif->hwaddr_len = ETHARP_HWADDR_LEN;
    netif->output = etharp_output;
    netif->linkoutput = lwip_eth_send;
    NETIF_INIT_SNMP(netif, snmp_ifType_ethernet_csmacd, LINK_SPEED);
    netif->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_LINK_UP | NETIF_FLAG_IGMP;

    return ERR_OK;
}

static void netif_status_callback(struct netif *netif)
{
    if (dhcp_supplied_address(netif)) {
        print("DHCP request finished, IP address for netif ");
        print(netif->name);
        print(" is: ");
        print(ip4addr_ntoa(netif_ip4_addr(netif)));
        print("\n");
    }
}

static void get_mac(void)
{
    /* For now just use a dummy hardcoded mac address.*/
    state.mac[0] = 0x52;
    state.mac[1] = 0x54;
    state.mac[2] = 0x1;
    state.mac[3] = 0;
    state.mac[4] = 0;
    state.mac[5] = 0;
    /* sel4cp_ppcall(RX_CH, sel4cp_msginfo_new(0, 0));
    uint32_t palr = sel4cp_mr_get(0);
    uint32_t paur = sel4cp_mr_get(1);
    state.mac[0] = palr >> 24;
    state.mac[1] = palr >> 16 & 0xff;
    state.mac[2] = palr >> 8 & 0xff;
    state.mac[3] = palr & 0xff;
    state.mac[4] = paur >> 24;
    state.mac[5] = paur >> 16 & 0xff;*/
}

void init_post(void)
{
    dump_mac(state.mac);
    netif_set_status_callback(&(state.netif), netif_status_callback);
    netif_set_up(&(state.netif));

    if (dhcp_start(&(state.netif))) {
        print("failed to start DHCP negotiation\n");
    }

    setup_udp_socket();
    setup_utilization_socket();

    print(sel4cp_name);
    print(": init complete -- waiting for notification\n");
}

void init(void)
{
    print(sel4cp_name);
    print(": elf PD init function running\n");

    /* Set up shared memory regions */
    ring_init(&state.rx_ring, (ring_buffer_t *)rx_free, (ring_buffer_t *)rx_used, NULL, 1);
    ring_init(&state.tx_ring, (ring_buffer_t *)tx_free, (ring_buffer_t *)tx_used, NULL, 1);


    for (int i = 0; i < NUM_BUFFERS - 1; i++) {
        ethernet_buffer_t *buffer = &state.buffer_metadata[i];
        *buffer = (ethernet_buffer_t) {
            .buffer = shared_dma_vaddr_rx + (BUF_SIZE * i),
            .size = BUF_SIZE,
            .origin = ORIGIN_RX_QUEUE,
            .index = i,
            .in_use = false,
        };
        int err = enqueue_free(&state.rx_ring, buffer->buffer, BUF_SIZE, buffer);
        assert(!err);
    }

    for (int i = 0; i < NUM_BUFFERS - 1; i++) {
        ethernet_buffer_t *buffer = &state.buffer_metadata[i + NUM_BUFFERS];
        *buffer = (ethernet_buffer_t) {
            .buffer = shared_dma_vaddr_tx + (BUF_SIZE * i),
            .size = BUF_SIZE,
            .origin = ORIGIN_TX_QUEUE,
            .index = i + NUM_BUFFERS,
            .in_use = false,
        };

        int err = enqueue_free(&state.tx_ring, buffer->buffer, BUF_SIZE, buffer);
        assert(!err);
    }

    lwip_init();

    gpt_init();

    LWIP_MEMPOOL_INIT(RX_POOL);

    get_mac();

    /* Set some dummy IP configuration values to get lwIP bootstrapped  */
    struct ip4_addr netmask, ipaddr, gw, multicast;
    ipaddr_aton("0.0.0.0", &gw);
    ipaddr_aton("0.0.0.0", &ipaddr);
    ipaddr_aton("0.0.0.0", &multicast);
    ipaddr_aton("255.255.255.0", &netmask);

    state.netif.name[0] = 'e';
    state.netif.name[1] = '0';

    if (!netif_add(&(state.netif), &ipaddr, &netmask, &gw, (void *)&state,
              ethernet_init, ethernet_input)) {
        print("Netif add returned NULL\n");
    }

    netif_set_default(&(state.netif));

    sel4cp_notify(RX_CH);
}

void notified(sel4cp_channel ch)
{
    switch(ch) {
        case RX_CH:
            process_rx_queue();
            break;
        case INIT:
            init_post();
            break;
        case IRQ:
            /* Timer */
            irq(ch);
            sel4cp_irq_ack(ch);
            break;
        case TX_CH:
            /*
             * We stop processing the Rx ring if there are no
             * Tx slots avilable.
             * Resume here.
             */
            if (!ring_empty(state.rx_ring.used_ring))
                process_rx_queue();
            break;
        default:
            sel4cp_dbg_puts("lwip: received notification on unexpected channel\n");
            assert(0);
            break;
    }
    if (notify_rx) {
        notify_rx = false;
        sel4cp_notify_delayed(RX_CH);
    }
    if (notify_tx) {
        notify_tx = false;
        if (!have_signal) {
            sel4cp_notify_delayed(TX_CH);
        } else if (signal != BASE_OUTPUT_NOTIFICATION_CAP + TX_CH){
            sel4cp_notify(TX_CH);
        }
    }
}
