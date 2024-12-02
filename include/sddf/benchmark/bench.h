/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

struct bench {
    // bench utilize
    uint64_t ccount;
    uint64_t prev;
    uint64_t ts;

    // driver
    uint64_t eth_pcount_tx; // # packets the driver transmits
    uint64_t eth_pcount_rx; // # packets the driver receives

    uint64_t eth_rx_irq_count; // # RX IRQs from NIC
    uint64_t eth_irq_count; // # IRQs from NIC

    uint64_t eth_rx_notified; // # RX_CH notification the driver receives
    uint64_t eth_idle_rx_notified; // same as above but nothing can be processed
    
    uint64_t eth_tx_notified; // # TX_CH notification the driver receives
    uint64_t eth_idle_tx_notified; // same as above but nothing can be processed

    uint64_t eth_rx_notify; // # RX_CH notification the driver sents

    uint64_t eth_request_signal_rx; // # times the driver requests signal from RX free
    uint64_t eth_rx_free_capacity; // to calculate the avg number of buffer in RX free
                                   // when the driver receive a RX_CH notification.
    uint64_t eth_rx_free_min_capacity;
    uint64_t eth_rx_free_max_capacity;

    // NIC
    uint64_t hw_pcount_rx; // # packets the NIC receives since START
    uint64_t hw_pcount_rx_dropped; // # packets the NIC drops since START

    // client0
    uint64_t lwip_pcount_tx;
    uint64_t lwip_pcount_rx;

    uint64_t lwip_rx_notify;
    uint64_t lwip_tx_notify;

    uint64_t lwip_rx_notified;
    uint64_t lwip_tx_notified;
    uint64_t lwip_idle_notified;

    // rx mux
    uint64_t rx_mux_notified;
    uint64_t rx_mux_idle_notified;

    // tx mux
    uint64_t tx_mux_notified;
    uint64_t tx_mux_idle_notified;
};
