/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

// @kwinter: This is for a basic inbound packet router.

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
#include <string.h>
#include "routing.h"
#include "arp.h"

uintptr_t arp_region;
arp_entry_t *arp_table;
uintptr_t routing_region;
routing_entry_t *routing_table;

uintptr_t arp_requests;
uintptr_t arp_replies;
/* Booleans to indicate whether packets have been enqueued during notification handling */
static bool notify_tx;
static bool notify_rx;

net_queue_handle_t filt_rx_queue;
net_queue_handle_t virt_tx_queue;

/* This queue will hold packets that we need to generate an ARP request for. */
net_queue_handle_t arp_waiting;
/* This queue will hold all the ARP requests/responses that are needed by the
packets in the arp_waiting queue. */
arp_queue_handle_t arp_request;
arp_queue_handle_t arp_response;


static char *ipaddr_to_string(uint32_t s_addr, char *buf, int buflen)
{
    char inv[3], *rp;
    uint8_t *ap, rem, n, i;
    int len = 0;

    rp = buf;
    ap = (uint8_t *)&s_addr;
    for (n = 0; n < 4; n++) {
        i = 0;
        do {
            rem = *ap % (uint8_t)10;
            *ap /= (uint8_t)10;
            inv[i++] = (char)('0' + rem);
        } while (*ap);
        while (i--) {
            if (len++ >= buflen) {
                return NULL;
            }
            *rp++ = inv[i];
        }
        if (len++ >= buflen) {
            return NULL;
        }
        *rp++ = '.';
        ap++;
    }
    *--rp = 0;
    return buf;
}

// @kwinter: Want a better way of doing this process. We seem to be doing alot of duplicate
// work.
void process_arp_waiting()
{
    /* Loop through all of the ARP responses. If there are any invalid
    responses we will drop the packets associated with the IP address. Otherwise
    we will substitute the MAC address in, and then send the packet out of the NIC. */

    while (!arp_queue_empty_response(&arp_query)) {
        arp_request_t response;
        int err = arp_dequeue_response(&arp_query, &response);

        if (!response.valid) {
            // Find all packets with this IP address and drop them.
            while(!net_queue_empty_free(&arp_waiting)) {
                net_buff_desc_t buffer;
                err = net_dequeue_free(&arp_waiting);
                assert(!err);
                // Check if the IP in this packet matches response.
                buffer.len = 0;
                err = net_enqueue_free(&filt_rx_queue, buffer);
                assert(!err);
            }
        } else {
            // We managed to get a valid MAC address back. Process
            // all packets with the associated IP address.
        }
    }

}

uint32_t find_route(uint32_t ip)
{
    // TODO: extend this function to match with the longest subnet mask,
    // and if tied in this step, find the route with the least hops.
    for (int i = 0; i < NUM_ROUTES; i++) {
        if ((ip & routing_table[i].subnet_mask) == (routing_table[i].network_id & routing_table[i].subnet_mask)) {
            // We have a match, return the next hop IP address.
            return routing_table[i].next_hop;
        }
    }

    // If we have gotten here, assume on the default gateway.
    return 0;
}

void route()
{
    // Check the IP address of the packet.
    bool transmitted = false;
    bool reprocess = true;
    while (reprocess) {
        while (!net_queue_empty_active(&filt_rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&filt_rx_queue, &buffer);
            assert(!err);

            struct ipv4_packet *pkt = (struct ethernet_header *)(net_config.rx_data.vaddr + buffer.io_or_offset);

            /* Decrement the TTL field. IF it reaches 0 protocol is that we drop
             * the packet in this router.
             *
             * NOTE: We assume that if we get a packet other than an IPv4 packet, we drop.buffer
             * This edge case should be handled by a new protocol virtualiser.
             */
            if (pkt->ttl > 1 && pkt->type == ETH_TYPE_IP) {
                pkt->ttl -= 1;
                // This is where we will swap out the MAC address with the appropriate address
                uint32_t destIP = pkt->dst_ip;
                // From the destination IP, consult the routing tables to find the next hop address.
                uint32_t nextIP = find_route(destIP);
                if (nextIP == 0) {
                    // If we have no route, assume that the device is attached directly.
                    nextIP = destIP;
                }
                uint8_t mac[ETH_HWADDR_LEN];
                mac = get_entry(arp_table, nextIP);

                if (mac == NULL) {
                    /* In this case, the IP address is not in the ARP Tables.
                    *  We add an entry to the ARP request queue. This is where we
                    *  place the responses to the ARP requests, and if we get a
                    *  timeout, we will then drop the packets associated with that IP address
                    *  that are waiting in the queue.
                    */

                    if (!arp_queue_empty_request(&arp_query)) {
                            arp_request_t request;

                            int ret = arp_dequeue_request(&arp_query, &request);
                            if (ret != 0) {
                                sddf_dprintf("ROUTING| No room in ARP request queue!\n");
                            }

                            request.ip_addr = nextIP;
                            ret = arp_enqueue_request(&arp_query, request);
                            if (ret != 0) {
                                sddf_dprintf("ROUTING| Unable to enqueue into ARP request queue!\n");
                            }

                    } else {
                            sddf_dprintf("ROUTING| ARP request queue was empty!\n");
                    }

                    // Add this packet to the ARP waiting queue.
                    if (!net_queue_full_free(&arp_waiting)) {
                        int ret = net_enqueue_free(&arp_waiting, buffer);
                        assert(!ret);
                    }
                } else {
                    // We should have the mac address. Replace the dest in the ethernet header.
                    for (int i = 0; i < ETH_HWADDR_LEN; i++) {
                        pkt->ethdst_addr[i] = mac[i];
                    }

                    // TODO: replace the source MAC address with the MAC address of our NIC.

                    // Send the packet out to the network.
                    net_buff_desc_t buffer;
                    int err = net_dequeue_free(&virt_tx_queue, &buffer);
                    assert(!err);
                    err = net_enqueue_active(&virt_tx_queue, buffer);
                    assert(!err);
                }

            }

            buffer.len = 0;
            err = net_enqueue_free(&filt_rx_queue, buffer);
            assert(!err);
        }

        net_request_signal_active(&filt_rx_queue);
        reprocess = false;

        if (!net_queue_empty_active(&filt_rx_queue)) {
            net_cancel_signal_active(&filt_rx_queue);
            reprocess = true;
        }
    }

    if (transmitted && net_require_signal_active(&virt_tx_queue)) {
        net_cancel_signal_active(&virt_tx_queue);
        microkit_deferred_notify(net_config.tx.id);
    }

}

void init(void)
{
    // Initialise the shared routing tables and zero them out.
    routing_table =  (routing_entry_t *) routing_region;
    sddf_memset((void *) routing_table, 0, (sizeof routing_entry_t) * NUM_ROUTES);
    // The internal ARP component should initialise this region.
    arp_table =  (arp_entry_t *) arp_region;
    // Init all net queues here as well as zero out the arp cache.
    /* @kwinter: Need to add a struct to meta.py defining all the regions our routing
        component might want to have access to. */

    // net_queue_init(&filt_rx_queue, net_config.rx.free_queue.vaddr, net_config.rx.active_queue.vaddr,
    //                net_config.rx.num_buffers);
    // net_queue_init(&virt_tx_queue, net_config.tx.free_queue.vaddr, net_config.tx.active_queue.vaddr,
    //                net_config.tx.num_buffers);
    // net_buffers_init(&virt_tx_queue, 0);

    /* @kwinter: We don't need this queue to be in shared memory. This queue just needs to be a temporary
     holding area while we wait for the ARP replies to come back. */

    /* TODO: also need to add in the arp request/response queue structs into the meta.py. */

    // arp_queue_init(&arp_queue, net_config.tx.free_queue.vaddr, net_config.tx.active_queue.vaddr,
    //                net_config.tx.num_buffers);
    // net_buffers_init(&arp_queue, 0);

}

void notified(microkit_channel ch)
{
    // Popualate with the rx ch number
    if (0) {
        route();
    } else if (1) {
        /* This is the channel between the ARP component and the routing component. */
        process_arp_waiting();
    }
}