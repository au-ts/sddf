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
#include "firewall_arp.h"
#include "hashmap.h"
#include "config.h"

__attribute__((__section__(".router_config"))) router_config_t router_config;
// Net2_client config will be for the tx out of NIC2
__attribute__((__section__(".net2_client_config"))) net_client_config_t net2_config;

hashtable_t *arp_table;
routing_entry_t routing_table[NUM_ROUTES] = {{0}};

/* Booleans to indicate whether packets have been enqueued during notification handling */
static bool notify_tx;
static bool notify_rx;

net_queue_handle_t virt_tx_queue;

typedef struct state {
    net_queue_handle_t filter_queue[61];
} state_t;

state_t state;

/* This queue will hold packets that we need to generate an ARP request for. */
net_queue_handle_t arp_waiting;
/* This queue will hold all the ARP requests/responses that are needed by the
packets in the arp_waiting queue. */
arp_queue_handle_t *arp_queries;

/* @kwinter: For now, we are just going to have one packet waiting on an ARP reply for this
    PoC. */
routing_queue_node_t waiting_packet = {0};

dev_info_t *device1_info;
dev_info_t *device2_info;

/* This code is taken from: https://gist.github.com/david-hoze/0c7021434796997a4ca42d7731a7073a*/
uint16_t checksum(uint8_t *buf, uint16_t len)
{
        uint32_t sum = 0;

        while(len >1){
                sum += 0xFFFF & (*buf<<8|*(buf+1));
                buf+=2;
                len-=2;
        }
        // if there is a byte left then add it (padded with zero)
        if (len){
        //  sum += (0xFF & *buf)<<8;
                sum += 0xFFFF & (*buf<<8|0x00);
        }
        // now calculate the sum over the bytes in the sum
        // until the result is only 16bit long
        while (sum>>16){
                sum = (sum & 0xFFFF)+(sum >> 16);
        }
        // build 1's complement:
        return( (uint16_t) sum ^ 0xFFFF);
}

// @kwinter: Want a better way of doing this process. We seem to be doing alot of duplicate
// work.
void process_arp_waiting()
{
    /* Loop through all of the ARP responses. If there are any invalid
    responses we will drop the packets associated with the IP address. Otherwise
    we will substitute the MAC address in, and then send the packet out of the NIC. */

    while (!arp_queue_empty_response(arp_queries)) {
        arp_request_t response;
        int err = arp_dequeue_response(arp_queries, &response);
        /* Check that we actually have a packet waiting. */
        if (!waiting_packet.valid) {
            continue;
        }

        if (!response.valid && waiting_packet.valid) {
            // Find all packets with this IP address and drop them.
            // net_buff_desc_t buffer = waiting_packet.buffer;
            // Check if the IP in this packet matches response.
            waiting_packet.buffer.len = 0;
            err = net_enqueue_free(&state.filter_queue[waiting_packet.filter], waiting_packet.buffer);
            assert(!err);
        } else {
            if (response.ip_addr == waiting_packet.ip) {
                // net_buff_desc_t buffer = waiting_packet.buffer;
                // @kwinter: This check is bad
                // if (waiting_packet.buffer.io_or_offset == 0) {
                //     sddf_dprintf("ROUTING|Error restoring buffer in process_arp_waiting()\n");
                //     return;
                // }
                struct ipv4_packet *pkt = (struct ipv4_packet *)(router_config.filters[waiting_packet.filter].data.vaddr + waiting_packet.buffer.io_or_offset);
                sddf_memcpy(pkt->ethdst_addr, response.mac_addr, ETH_HWADDR_LEN);
                sddf_memcpy(pkt->ethsrc_addr, device2_info->mac, ETH_HWADDR_LEN);
                net_buff_desc_t buffer_tx;
                int err = net_dequeue_free(&virt_tx_queue, &buffer_tx);
                assert(!err);
                pkt->check = 0;
                pkt->check = checksum((uint8_t *)pkt, 20);

                // @kwinter: For now we are memcpy'ing the packet from our receive buffer
                // to the transmit buffer.
                // Also need to make sure that len here is the appropriate size.
                sddf_memcpy((net2_config.tx_data.vaddr + buffer_tx.io_or_offset), (router_config.filters[waiting_packet.filter].data.vaddr + waiting_packet.buffer.io_or_offset), waiting_packet.buffer.len);
                buffer_tx.len = waiting_packet.buffer.len;
                err = net_enqueue_active(&virt_tx_queue, buffer_tx);
                assert(!err);
                waiting_packet.buffer.len = 0;
                err = net_enqueue_free(&state.filter_queue[waiting_packet.filter], waiting_packet.buffer);
                assert(!err);
                microkit_deferred_notify(net2_config.tx.id);

            }
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
    for (int filter = 0; filter < router_config.num_filters; filter++) {
        bool reprocess = true;
        while (reprocess) {
            sddf_dprintf("This is the filter id: %d\n", filter);
            while (!net_queue_empty_active(&state.filter_queue[filter])) {
                sddf_dprintf("LOOOOOOOPING\n");
                net_buff_desc_t buffer;
                int err = net_dequeue_active(&state.filter_queue[filter], &buffer);
                assert(!err);

                struct ipv4_packet *pkt = (struct ipv4_packet *)(router_config.filters[filter].data.vaddr + buffer.io_or_offset);

                /* Decrement the TTL field. IF it reaches 0 protocol is that we drop
                * the packet in this router.
                *
                * NOTE: We assume that if we get a packet other than an IPv4 packet, we drop.buffer
                * This edge case should be handled by a new protocol virtualiser.
                */
                // if (pkt->ttl > 1 && pkt->type == ETH_TYPE_IP) {
                if (pkt->type == HTONS(ETH_TYPE_IP)) {
                    sddf_dprintf("ROUTING|We got the right kind of packet!\n");
                    pkt->ttl -= 1;
                    // This is where we will swap out the MAC address with the appropriate address
                    uint32_t destIP = pkt->dst_ip;
                    // @kwinter: Remove this debug filter
                    if (destIP != IPV4_ADDR(192,168,33,6)) {
                        continue;
                    }

                    // From the destination IP, consult the routing tables to find the next hop address.
                    uint32_t nextIP = find_route(destIP);
                    if (nextIP == 0) {
                        // If we have no route, assume that the device is attached directly.
                        nextIP = destIP;
                    }
                    uint8_t mac[ETH_HWADDR_LEN];
                    arp_entry_t hash_entry;
                    int ret = hashtable_search(arp_table, (uint32_t) nextIP, &hash_entry);
                    if (ret == -1 && waiting_packet.valid == false) {
                        hashtable_empty(arp_table);
                        /* In this case, the IP address is not in the ARP Tables.
                        *  We add an entry to the ARP request queue. This is where we
                        *  place the responses to the ARP requests, and if we get a
                        *  timeout, we will then drop the packets associated with that IP address
                        *  that are waiting in the queue.
                        */

                        if (!arp_queue_full_request(arp_queries)) {
                                arp_request_t request = {0};
                                request.ip_addr = nextIP;
                                request.valid = true;
                                char buf[16];
                                int ret = arp_enqueue_request(arp_queries, request);
                                if (ret != 0) {
                                    sddf_dprintf("ROUTING| Unable to enqueue into ARP request queue!\n");
                                }
                        } else {
                                sddf_dprintf("ROUTING| ARP request queue was full!\n");
                                buffer.len = 0;
                                err = net_enqueue_free(&state.filter_queue[filter], buffer);
                                assert(!err);
                                continue;
                        }

                        // Add this packet to the ARP waiting node.
                        waiting_packet.ip = nextIP;
                        sddf_memcpy(&waiting_packet.buffer, &buffer, sizeof(net_buff_desc_t));
                        waiting_packet.buffer = buffer;
                        waiting_packet.valid = true;
                        waiting_packet.filter = filter;
                        microkit_deferred_notify(router_config.router.id);
                        continue;
                    } else {
                        // We should have the mac address. Replace the dest in the ethernet header.
                        sddf_memcpy(&pkt->ethdst_addr, &hash_entry.mac_addr, ETH_HWADDR_LEN);
                        // TODO: replace the source MAC address with the MAC address of our NIC.
                        sddf_memcpy(&pkt->ethsrc_addr, device2_info->mac, ETH_HWADDR_LEN);
                        pkt->check = 0;
                        pkt->check = checksum((uint8_t *)pkt, 20);
                        // Send the packet out to the network.
                        net_buff_desc_t buffer_tx;
                        // @kwinter: TODO: This should be a predicate for out loop, that we have
                        // room in the tx queue.
                        int err = net_dequeue_free(&virt_tx_queue, &buffer_tx);
                        assert(!err);

                        // @kwinter: For now we are memcpy'ing the packet from our receive buffer
                        // to the transmit buffer.
                        // Also need to make sure that len here is the appropriate size.
                        sddf_memcpy((net2_config.tx_data.vaddr + buffer_tx.io_or_offset), (router_config.filters[filter].data.vaddr + buffer.io_or_offset), buffer.len + (sizeof(struct ipv4_packet)));
                        struct ipv4_packet *test = (struct ipv4_packet *)(net2_config.tx_data.vaddr + buffer_tx.io_or_offset);
                        buffer_tx.len = buffer.len;
                        err = net_enqueue_active(&virt_tx_queue, buffer_tx);
                        transmitted = true;

                        assert(!err);
                    }
                    buffer.len = 0;
                    err = net_enqueue_free(&state.filter_queue[filter], buffer);
                    assert(!err);

                } else {
                    sddf_dprintf("ROUTING|We got the worng kind of packet\n");
                }
            }

            net_request_signal_active(&state.filter_queue[filter]);
            reprocess = false;

            if (!net_queue_empty_active(&state.filter_queue[filter])) {
                net_cancel_signal_active(&state.filter_queue[filter]);
                reprocess = true;
            }
        }
    }

    if (transmitted && net_require_signal_active(&virt_tx_queue)) {
        net_cancel_signal_active(&virt_tx_queue);
        microkit_deferred_notify(net2_config.tx.id);
    }

}

void init(void)
{
    sddf_dprintf("Initialising our routing component\n");
    // Init the hashtable here, as we are the first component that will
    // ever access it.
    assert(net_config_check_magic((void *)&net2_config));
    assert(firewall_config_check_magic((void*) &router_config));
    arp_table = (hashtable_t*) router_config.router.arp_cache.vaddr;
    hashtable_init(arp_table);

    // Setup all the queues for the filters
    for (int i = 0; i < router_config.num_filters; i++) {
        net_queue_init(&state.filter_queue[i], router_config.filters[i].conn.free_queue.vaddr,
            router_config.filters[i].conn.active_queue.vaddr, router_config.filters[i].conn.num_buffers);
    }
    net_queue_init(&virt_tx_queue, net2_config.tx.free_queue.vaddr, net2_config.tx.active_queue.vaddr,
        net2_config.tx.num_buffers);
    net_buffers_init(&virt_tx_queue, 0);

    arp_queries = (arp_queue_handle_t *) router_config.router.arp_queue.vaddr;
    arp_handle_init(arp_queries, 256);

    device2_info = (dev_info_t *) net2_config.dev_info.vaddr;

    // routing_table[0].network_id = 0;
    // routing_table[0].subnet_mask = 0xFFFFFF00;
    // routing_table[0].next_hop = 0;
    sddf_dprintf("Finished init in the routing component. This is the number of filter: %d\n", router_config.num_filters);
}

void notified(microkit_channel ch)
{
    // Popualate with the rx ch number
    if (ch == router_config.router.id) {
        /* This is the channel between the ARP component and the routing component. */
        process_arp_waiting();
    } else {
        sddf_dprintf("Getting notified to route a packet!\n");
        route();
    }
}
