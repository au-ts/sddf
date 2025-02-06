/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/network/util.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/benchmark/sel4bench.h>
#include <sddf/benchmark/config.h>
#include <string.h>
#include "lwip/init.h"
#include "netif/etharp.h"
#include "lwip/pbuf.h"
#include "lwip/netif.h"
#include "lwip/stats.h"
#include "lwip/snmp.h"
#include "lwip/sys.h"
#include "lwip/timeouts.h"
#include "lwip/dhcp.h"

#include "echo.h"

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
__attribute__((__section__(".net_client_config"))) net_client_config_t net_config;
__attribute__((__section__(".benchmark_client_config"))) benchmark_client_config_t benchmark_config;

serial_queue_handle_t serial_tx_queue_handle;

#define LWIP_TICK_MS 100
#define NUM_PBUFFS 512 // TODO: make dynamic

/* Booleans to indicate whether packets have been enqueued during notification handling */
static bool notify_tx;
static bool notify_rx;

/* Wrapper over custom_pbuf structure to keep track of buffer offset */
typedef struct pbuf_custom_offset {
    struct pbuf_custom custom;
    uint64_t offset;
} pbuf_custom_offset_t;

LWIP_MEMPOOL_DECLARE(
    RX_POOL,
    NUM_PBUFFS * 2,
    sizeof(struct pbuf_custom_offset),
    "Zero-copy RX pool"
);

typedef struct state {
    struct netif netif;
    uint8_t mac[ETH_HWADDR_LEN];
    net_queue_handle_t rx_queue;
    net_queue_handle_t tx_queue;
    struct pbuf *head;
    struct pbuf *tail;
} state_t;

state_t state;

void set_timeout(void)
{
    sddf_timer_set_timeout(timer_config.driver_id, LWIP_TICK_MS * NS_IN_MS);
}

uint32_t sys_now(void)
{
    return sddf_timer_time_now(timer_config.driver_id) / NS_IN_MS;
}

/**
 * Free a pbuf. This also returns the underlying buffer to the receive free ring.
 *
 * @param p pbuf to free.
 */
static void interface_free_buffer(struct pbuf *p)
{
    SYS_ARCH_DECL_PROTECT(old_level);
    pbuf_custom_offset_t *custom_pbuf_offset = (pbuf_custom_offset_t *)p;
    SYS_ARCH_PROTECT(old_level);
    net_buff_desc_t buffer = {custom_pbuf_offset->offset, 0};
    int err = net_enqueue_free(&(state.rx_queue), buffer);
    assert(!err);
    notify_rx = true;
    LWIP_MEMPOOL_FREE(RX_POOL, custom_pbuf_offset);
    SYS_ARCH_UNPROTECT(old_level);
}

/**
 * Create a pbuf structure to pass to the network interface.
 *
 * @param state client state data.
 * @param buffer shared buffer containing the data.
 * @param length length of data.
 *
 * @return the newly created pbuf. Can be cast to pbuf_custom.
 */
static struct pbuf *create_interface_buffer(uint64_t offset, size_t length)
{
    pbuf_custom_offset_t *custom_pbuf_offset = (pbuf_custom_offset_t *) LWIP_MEMPOOL_ALLOC(RX_POOL);
    custom_pbuf_offset->offset = offset;
    custom_pbuf_offset->custom.custom_free_function = interface_free_buffer;

    return pbuf_alloced_custom(PBUF_RAW, length, PBUF_REF, &custom_pbuf_offset->custom,
                               (void *)(offset + net_config.rx_data.vaddr), NET_BUFFER_SIZE);
}

/**
 * Stores a pbuf to be transmitted upon available transmit buffers.
 *
 * @param p pbuf to be stored.
 */
void enqueue_pbufs(struct pbuf *p)
{
    /* Indicate to the multiplexer that we require transmit free buffers */
    net_request_signal_free(&state.tx_queue);

    if (state.head == NULL) {
        state.head = p;
    } else {
        state.tail->next_chain = p;
    }
    state.tail = p;

    /* Increment refernce count to ensure this pbuf is not freed by lwip */
    pbuf_ref(p);
}

/**
 * Insert pbuf into transmit active queue. If no free buffers available or transmit active queue is full,
 * stores pbuf to be sent upon buffers becoming available.
 * */
static err_t lwip_eth_send(struct netif *netif, struct pbuf *p)
{
    if (p->tot_len > NET_BUFFER_SIZE) {
        sddf_dprintf("LWIP|ERROR: attempted to send a packet of size  %u > BUFFER SIZE  %u\n", p->tot_len, NET_BUFFER_SIZE);
        return ERR_MEM;
    }

    if (net_queue_empty_free(&state.tx_queue)) {
        enqueue_pbufs(p);
        return ERR_OK;
    }

    net_buff_desc_t buffer;
    int err = net_dequeue_free(&state.tx_queue, &buffer);
    assert(!err);

    void *frame = buffer.io_or_offset + net_config.tx_data.vaddr;
    uint16_t copied = 0;
    for (struct pbuf *curr = p; curr != NULL; curr = curr->next) {
        memcpy(frame + copied, curr->payload, curr->len);
        copied += curr->len;
    }

    buffer.len = copied;
    err = net_enqueue_active(&state.tx_queue, buffer);
    assert(!err);

    notify_tx = true;

    return ERR_OK;
}

void transmit(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (state.head != NULL && !net_queue_empty_free(&state.tx_queue)) {
            err_t err = lwip_eth_send(&state.netif, state.head);
            if (err == ERR_MEM) {
                sddf_dprintf("LWIP|ERROR: attempted to send a packet of size  %u > BUFFER SIZE  %u\n", state.head->tot_len,
                             NET_BUFFER_SIZE);
            } else if (err != ERR_OK) {
                sddf_dprintf("LWIP|ERROR: unkown error when trying to send pbuf  %p\n", state.head);
            }

            struct pbuf *temp = state.head;
            state.head = temp->next_chain;
            if (state.head == NULL) {
                state.tail = NULL;
            }
            pbuf_free(temp);
        }

        /* Only request a signal if no more pbufs enqueud to send */
        if (state.head == NULL || !net_queue_empty_free(&state.tx_queue)) {
            net_cancel_signal_free(&state.tx_queue);
        } else {
            net_request_signal_free(&state.tx_queue);
        }
        reprocess = false;

        if (state.head != NULL && !net_queue_empty_free(&state.tx_queue)) {
            net_cancel_signal_free(&state.tx_queue);
            reprocess = true;
        }
    }
}

void receive(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (!net_queue_empty_active(&state.rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&state.rx_queue, &buffer);
            assert(!err);

            struct pbuf *p = create_interface_buffer(buffer.io_or_offset, buffer.len);
            assert(p != NULL);
            if (state.netif.input(p, &state.netif) != ERR_OK) {
                sddf_dprintf("LWIP|ERROR: unkown error inputting pbuf into network stack\n");
                pbuf_free(p);
            }
        }

        net_request_signal_active(&state.rx_queue);
        reprocess = false;

        if (!net_queue_empty_active(&state.rx_queue)) {
            net_cancel_signal_active(&state.rx_queue);
            reprocess = true;
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

/* Callback function that prints DHCP supplied IP address. */
static void netif_status_callback(struct netif *netif)
{
    if (dhcp_supplied_address(netif)) {
        sddf_printf("LWIP|NOTICE: DHCP request for %s returned IP address: %s\n", microkit_name,
                    ip4addr_ntoa(netif_ip4_addr(netif)));
    }
}

void init(void)
{
    assert(serial_config_check_magic(&serial_config));
    assert(net_config_check_magic(&net_config));
    assert(timer_config_check_magic(&timer_config));

    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

    net_queue_init(&state.rx_queue, net_config.rx.free_queue.vaddr, net_config.rx.active_queue.vaddr,
                   net_config.rx.num_buffers);
    net_queue_init(&state.tx_queue, net_config.tx.free_queue.vaddr, net_config.tx.active_queue.vaddr,
                   net_config.tx.num_buffers);
    net_buffers_init(&state.tx_queue, 0);

    lwip_init();
    set_timeout();

    LWIP_MEMPOOL_INIT(RX_POOL);

    sddf_memcpy(state.mac, net_config.mac_addr, 6);

    /* Set dummy IP configuration values to get lwIP bootstrapped  */
    struct ip4_addr netmask, ipaddr, gw, multicast;
    ipaddr_aton("0.0.0.0", &gw);
    ipaddr_aton("0.0.0.0", &ipaddr);
    ipaddr_aton("0.0.0.0", &multicast);
    ipaddr_aton("255.255.255.0", &netmask);

    state.netif.name[0] = 'e';
    state.netif.name[1] = '0';

    if (!netif_add(&(state.netif), &ipaddr, &netmask, &gw, (void *)&state,
                   ethernet_init, ethernet_input)) {
        sddf_dprintf("LWIP|ERROR: Netif add returned NULL\n");
    }

    netif_set_default(&(state.netif));
    netif_set_status_callback(&(state.netif), netif_status_callback);
    netif_set_up(&(state.netif));

    if (dhcp_start(&(state.netif))) {
        sddf_dprintf("LWIP|ERROR: failed to start DHCP negotiation\n");
    }

    setup_udp_socket();
    setup_utilization_socket(benchmark_config.cycle_counters, benchmark_config.start_ch, benchmark_config.stop_ch);
    setup_tcp_socket();

    if (notify_rx && net_require_signal_free(&state.rx_queue)) {
        net_cancel_signal_free(&state.rx_queue);
        notify_rx = false;
        if (!microkit_have_signal) {
            microkit_deferred_notify(net_config.rx.id);
        } else if (microkit_signal_cap != BASE_OUTPUT_NOTIFICATION_CAP + net_config.rx.id) {
            microkit_notify(net_config.rx.id);
        }
    }

    if (notify_tx && net_require_signal_active(&state.tx_queue)) {
        net_cancel_signal_active(&state.tx_queue);
        notify_tx = false;
        if (!microkit_have_signal) {
            microkit_deferred_notify(net_config.tx.id);
        } else if (microkit_signal_cap != BASE_OUTPUT_NOTIFICATION_CAP + net_config.tx.id) {
            microkit_notify(net_config.tx.id);
        }
    }
}

void notified(microkit_channel ch)
{
    if (ch == net_config.rx.id) {
        receive();
    } else if (ch == net_config.tx.id) {
        transmit();
        receive();
    } else if (ch == timer_config.driver_id) {
        sys_check_timeouts();
        set_timeout();
    } else if (ch == serial_config.tx.id) {
        // Nothing to do
    } else {
        sddf_dprintf("LWIP|LOG: received notification on unexpected channel: %u\n", ch);
    }

    if (notify_rx && net_require_signal_free(&state.rx_queue)) {
        net_cancel_signal_free(&state.rx_queue);
        notify_rx = false;
        if (!microkit_have_signal) {
            microkit_deferred_notify(net_config.rx.id);
        } else if (microkit_signal_cap != BASE_OUTPUT_NOTIFICATION_CAP + net_config.rx.id) {
            microkit_notify(net_config.rx.id);
        }
    }

    if (notify_tx && net_require_signal_active(&state.tx_queue)) {
        net_cancel_signal_active(&state.tx_queue);
        notify_tx = false;
        if (!microkit_have_signal) {
            microkit_deferred_notify(net_config.tx.id);
        } else if (microkit_signal_cap != BASE_OUTPUT_NOTIFICATION_CAP + net_config.tx.id) {
            microkit_notify(net_config.tx.id);
        }
    }
}
