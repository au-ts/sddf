/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/util/util.h>
#include <string.h>
#include <sddf/util/printf.h>
#include <sddf/network/lib_sddf_lwip.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/benchmark/config.h>
#include <sddf/benchmark/bench.h>
#include "lwip/pbuf.h"
#include "lwip/ip_addr.h"
#include "lwip/stats.h"

#include "iperf3_ctrl.h"
#include "iperf3_app.h"
/* iperf3_util.h declares the ipbench utilization socket + port (protocol
 * agnostic), wanted for both TCP and UDP builds. */
#include "iperf3_util.h"

__attribute__((__section__(".iperf3_app_config"))) iperf3_app_config_t app_config;

static bool iperf3_started = false;

static uint64_t bench_core_start[CONFIG_MAX_NUM_NODES];
static uint64_t bench_idle_start[CONFIG_MAX_NUM_NODES];
static bool bench_snapshotted;
static bool bench_reported;

/* Exact TX packet count over the measurement window, from lwIP stats
 * (tcp.xmit = TCP segments sent; counted in core tcp_output). */
static uint32_t pkts_segs_start;
static bool pkts_snapshotted, pkts_reported;

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
__attribute__((__section__(".net_client_config"))) net_client_config_t net_config;
__attribute__((__section__(".benchmark_client_config"))) benchmark_client_config_t benchmark_config;
__attribute__((__section__(".lib_sddf_lwip_config"))) lib_sddf_lwip_config_t lib_sddf_lwip_config;

serial_queue_handle_t serial_tx_queue_handle;
net_queue_handle_t net_rx_handle;
net_queue_handle_t net_tx_handle;

static iperf_ctrl_t ctrl;

#define LWIP_TICK_MS 100

static uint32_t prng_state = 0x12345678;

static uint32_t prng_next(void) {
    prng_state = prng_state * 1103515245u + 12345u;
    return prng_state;
}

static void make_cookie(uint8_t *cookie) {
    static const char chars[] = "abcdefghijklmnopqrstuvwxyz0123456789";
    for (int i = 0; i < IPERF3_COOKIE_LEN; i++) {
        cookie[i] = chars[prng_next() % (sizeof(chars) - 1)];
    }
}

void netif_status_callback(char *ip_addr)
{
    sddf_printf("DHCP request finished, IP address for netif %s is: %s\n",
                sddf_get_pd_name(), ip_addr);

    if (!iperf3_started) {
        iperf3_started = true;

        /* Server address/port come from the injected per-client app config so
         * that each copied client ELF (client0, client1, ...) can target a
         * different iperf3 server. Fall back to 10.0.2.2:5202 when unset
         * (e.g. SERVER_IP_x compile defaults still honoured for the address). */
#ifndef SERVER_IP_A
#define SERVER_IP_A 10
#define SERVER_IP_B 0
#define SERVER_IP_C 2
#define SERVER_IP_D 2
#endif
        ip_addr_t server_addr;
        uint16_t server_port = app_config.server_port ? app_config.server_port : 5202;
        if (app_config.server_ip[0] || app_config.server_ip[1] ||
            app_config.server_ip[2] || app_config.server_ip[3]) {
            IP_ADDR4(&server_addr, app_config.server_ip[0], app_config.server_ip[1],
                     app_config.server_ip[2], app_config.server_ip[3]);
        } else {
            IP_ADDR4(&server_addr, SERVER_IP_A, SERVER_IP_B, SERVER_IP_C, SERVER_IP_D);
        }
        sddf_printf("Starting iperf3 (%s) client %u now — server %s:%u\n",
#ifdef IPERF3_UDP
                    "UDP",
#else
                    "TCP",
#endif
                    app_config.client_id, ip4addr_ntoa(&server_addr), server_port);

        struct tcp_pcb *pcb = tcp_new_ip_type(IPADDR_TYPE_V4);
        if (pcb == NULL) {
            sddf_printf("iperf3_client: failed to create PCB\n");
            return;
        }
        err_t error = tcp_bind(pcb, IP_ANY_TYPE, 0);
        if (error) {
            sddf_printf("Failed to bind TCP socket: %s\n", lwip_strerr(error));
            return;
        }
        iperf3_ctrl_init(&ctrl);
        ctrl.server_port = server_port;
        tcp_arg(pcb, &ctrl);
        make_cookie(ctrl.cookie);
        error = tcp_connect(pcb, &server_addr, server_port, iperf_ctrl_connect);
        if (error) {
            sddf_printf("Failed to connect TCP control socket: %s\n", lwip_strerr(error));
            return;
        }
    }
}

static void set_timeout(void)
{
    sddf_timer_set_timeout(timer_config.driver_id, LWIP_TICK_MS * NS_IN_MS);
}

void init(void)
{
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr,
                      serial_config.tx.data.size, serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

    net_queue_init(&net_rx_handle, net_config.rx.free_queue.vaddr,
                   net_config.rx.active_queue.vaddr, net_config.rx.num_buffers);
    net_queue_init(&net_tx_handle, net_config.tx.free_queue.vaddr,
                   net_config.tx.active_queue.vaddr, net_config.tx.num_buffers);
    net_buffers_init(&net_tx_handle, 0);

    sddf_lwip_init(&lib_sddf_lwip_config, &net_config, &timer_config,
                   net_rx_handle, net_tx_handle, NULL, NULL,
                   netif_status_callback, NULL, NULL, NULL);
    set_timeout();
    /* ipbench-compatible CPU-utilisation socket - works for both TCP and UDP */
    setup_utilization_socket(&benchmark_config);
#ifdef IPERF3_UDP
    sddf_printf("MEMP_NUM_UDP_PCB = %d\n", MEMP_NUM_UDP_PCB);
#endif
    sddf_lwip_maybe_notify();
}

void notified(sddf_channel ch)
{
    if (ch == net_config.rx.id) {
        sddf_lwip_process_rx();
    } else if (ch == timer_config.driver_id) {
        sddf_lwip_process_timeout();
        uint32_t now_ms = sddf_timer_time_now(timer_config.driver_id) / 1000000;
#ifdef IPERF3_UDP
        for (int s = 0; s < MAX_STREAMS; s++) {
            ctrl.udp_streams[s].packets_this_tick = 0;
        }
        iperf3_on_timer_tick(&ctrl, now_ms);
        if (ctrl.test_active && !ctrl.test_done) {
            net_request_signal_free(&net_tx_handle);
        }
#else /* IPERF3_TCP */
        for (int s = 0; s < MAX_STREAMS; s++) {
            if (ctrl.streams[s].pcb != NULL && ctrl.streams[s].phase == SEND_PAYLOAD) {
                ctrl.streams[s].bytes_this_tick = 0;
                iperf3_stream_maybe_tx(&ctrl.streams[s]);
            }
        }
        (void)now_ms;
#endif
        set_timeout();
    } else if (ch == serial_config.tx.id) {
        /* nothing */
#ifdef IPERF3_UDP
    } else if (ch == net_config.tx.id) {
        /* TX buffers freed — continue pumping remaining tick budget */
        uint32_t now_ms = sddf_timer_time_now(timer_config.driver_id) / 1000000;
        iperf3_on_timer_tick(&ctrl, now_ms);
        if (ctrl.test_active && !ctrl.test_done) {
            net_request_signal_free(&net_tx_handle);
        }
#endif
    } else {
        sddf_dprintf("LWIP|LOG: received notification on unexpected channel: %u\n", ch);
    }

#ifndef IPERF3_UDP
    /* A client placed on a non-timer core never receives timer notifications
     * (the passive timer driver's signal does not cross cores), so the
     * timer-driven deadline check (iperf_poll) never runs there and the test
     * would never end. Evaluate the deadline from the data path instead: network
     * notifications keep arriving while the streams send, and the GET_TIME PPC
     * works cross-core. Throttled so the PPC cost stays off the CPU-util window.
     * (UDP already gets this via its net_tx branch above.) */
    if (ctrl.test_active && !ctrl.sent_test_end) {
        static uint32_t deadline_throttle = 0;
        if ((deadline_throttle++ & 0x3F) == 0) {
            uint32_t now_ms = sddf_timer_time_now(timer_config.driver_id) / 1000000;
            iperf3_tcp_check_deadline(&ctrl, now_ms);
        }
    }
#endif

    sddf_lwip_maybe_notify();

    /* Snapshot every active core's idle-PD counters once the warm-up (omit)
     * period is over, so the cycle window matches iperf3's measurement window
     * (omit is excluded from the reported throughput, so it must be excluded
     * here too). Notifying start_ch here also resets the benchmark PDs' PMU /
     * utilisation counters at the same boundary. Only client0 has num_cores > 0. */
    if (ctrl.test_active && !ctrl.omitting && !bench_snapshotted && benchmark_config.num_cores > 0) {
        for (uint8_t c = 0; c < benchmark_config.num_cores; c++) {
            struct bench *b = (struct bench *)benchmark_config.core_ccounts[c];
            bench_core_start[c] = __atomic_load_n(&b->core_ccount, __ATOMIC_RELAXED);
            bench_idle_start[c] = __atomic_load_n(&b->idle_ccount, __ATOMIC_RELAXED);
        }
        bench_snapshotted = true;
        microkit_notify(benchmark_config.start_ch);
    }

    /* TX packet count (lwIP tcp.xmit) over the post-omit window — snapshot at
     * omit_end, report before MQ_EXIT so the machine queue captures it. */
    if (ctrl.test_active && !ctrl.omitting && !pkts_snapshotted) {
        pkts_segs_start = lwip_stats.tcp.xmit;
        pkts_snapshotted = true;
    }
    if (pkts_snapshotted && ctrl.sent_test_end && !pkts_reported) {
        pkts_reported = true;
        sddf_printf("[pkts] client=%u tx_segs=%u\n", app_config.client_id,
                    (uint32_t)(lwip_stats.tcp.xmit - pkts_segs_start));
    }

    /* Report aggregate (summed across all cores) when TEST_END has been sent */
    if (bench_snapshotted && ctrl.sent_test_end && !bench_reported) {
        microkit_notify(benchmark_config.stop_ch);
        bench_reported = true;

        if (benchmark_config.num_cores > 0) {
            uint64_t total = 0, idle = 0;
            for (uint8_t c = 0; c < benchmark_config.num_cores; c++) {
                struct bench *b = (struct bench *)benchmark_config.core_ccounts[c];
                total += __atomic_load_n(&b->core_ccount, __ATOMIC_RELAXED) - bench_core_start[c];
                idle  += __atomic_load_n(&b->idle_ccount, __ATOMIC_RELAXED) - bench_idle_start[c];
            }
            if (total > 0) {
                double util = (double)(total - idle) / (double)total * 100.0;
                sddf_printf("[cpu_util] %.1f%% over %u core(s) (busy=%llu idle=%llu total=%llu cycles)\n",
                    util, benchmark_config.num_cores,
                    (unsigned long long)(total - idle),
                    (unsigned long long)idle,
                    (unsigned long long)total);
#ifndef IPERF3_UDP
                /* TCP stores it so EXCHANGE_RESULTS JSON can report it */
                ctrl.cpu_util_percent = util;
#endif
            } else {
                sddf_printf("[cpu_util] no data — build with MICROKIT_CONFIG=benchmark/smp-benchmark\n");
            }
        }
#ifndef IPERF3_UDP
        /* Print RTT before MQ_EXIT so the machine queue (which stops capturing at
         * the MQ_EXIT completion string) records it. RTT is fully accumulated by
         * TEST_END. (UDP has no ACK round-trips, so no RTT — jitter is its metric.) */
        {
            uint32_t mn, mean, mx, sd; uint64_t n;
            iperf3_tcp_rtt_aggregate(&ctrl, &mn, &mean, &mx, &sd, &n);
            sddf_printf("[rtt] min=%u mean=%u max=%u sd=%u us (n=%llu)\n",
                        mn, mean, mx, sd, (unsigned long long)n);
        }
#endif
        sddf_printf("MQ_EXIT\n");
    }

}
