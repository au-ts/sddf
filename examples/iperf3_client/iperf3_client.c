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
#include "iperf3_multi.h"
/* iperf3_util.h declares the ipbench utilization socket + port (protocol
 * agnostic), wanted for both TCP and UDP builds. */
#include "iperf3_util.h"

__attribute__((__section__(".iperf3_app_config"))) iperf3_app_config_t app_config;

/* Multi-client coordination: in a multi-client build only client0 (the
 * controller) gets serial input; it broadcasts the parsed test params to the
 * other clients via the shared region + per-peer notifications. */
__attribute__((__section__(".iperf3_multi_config"))) iperf3_multi_config_t multi_config;
static volatile iperf3_shared_params_t *shared_params =
    (volatile iperf3_shared_params_t *)IPERF3_SHARED_PARAMS_VADDR;
static uint32_t shared_gen_local;   /* controller: last generation it published */
static uint32_t shared_gen_seen;    /* peer: last generation it acted on */

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
serial_queue_handle_t serial_rx_queue_handle;
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

static bool netif_ready = false;

#ifdef IPERF3_UDP
#define PROTO_STR "UDP"
#define DEFAULT_DURATION_S 5
#else
#define PROTO_STR "TCP"
#define DEFAULT_DURATION_S 10
#endif

/* Emit a string with sddf_putchar_unbuffered so it is flushed immediately.
 * sddf_printf is line-buffered (flushes only on '\n'), so a prompt with no
 * trailing newline would otherwise never reach the console. */
static void serial_write_unbuffered(const char *s)
{
    while (*s) {
        sddf_putchar_unbuffered(*s++);
    }
}

static void print_prompt(void)
{
    serial_write_unbuffered("\niperf3> ");
}

/* Open the control connection and kick off a test against server a.b.c.d:port
 * with the given runtime parameters. Replaces the old auto-start path; called
 * from the serial `start` command handler. */
static void iperf3_begin_test(uint8_t a, uint8_t b, uint8_t c, uint8_t d,
                              uint16_t port, uint32_t duration_s,
                              uint8_t num_streams, uint32_t bw_mbps,
                              uint16_t payload_len)
{
    if (!netif_ready) {
        sddf_printf("network is not up yet — wait for the DHCP message\n");
        return;
    }
    if (ctrl.test_active && !ctrl.sent_test_end) {
        sddf_printf("a test is already running — wait for it to finish\n");
        return;
    }

    ip_addr_t server_addr;
    IP_ADDR4(&server_addr, a, b, c, d);

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
    ctrl.server_port = port;
    ctrl.duration_s = duration_s;
    ctrl.num_streams = num_streams;
    ctrl.target_bw_mbps = bw_mbps;
    ctrl.payload_len = payload_len;
#ifdef IPERF3_UDP
    ctrl.omit_s = 0;
#else
    ctrl.omit_s = 5;
#endif

    /* Allow a fresh CPU-util / packet-count measurement for each run. */
    bench_snapshotted = bench_reported = false;
    pkts_snapshotted = pkts_reported = false;

    tcp_arg(pcb, &ctrl);
    make_cookie(ctrl.cookie);

    sddf_printf("Starting iperf3 (%s) -> %u.%u.%u.%u:%u  dur=%us streams=%u bw=%uM len=%u\n",
                PROTO_STR, a, b, c, d, port, duration_s, num_streams, bw_mbps, payload_len);

    error = tcp_connect(pcb, &server_addr, port, iperf_ctrl_connect);
    if (error) {
        sddf_printf("Failed to connect TCP control socket: %s\n", lwip_strerr(error));
        return;
    }
}

/* ---- tiny command-line parsing (no libc strtok/atoi) ---- */

/* If `line` begins with `word` followed by a space or end-of-string, return a
 * pointer just past the word; otherwise NULL. */
static char *match_word(char *line, const char *word)
{
    int i = 0;
    while (word[i]) {
        if (line[i] != word[i]) return NULL;
        i++;
    }
    if (line[i] != '\0' && line[i] != ' ') return NULL;
    return line + i;
}

/* Parse a decimal uint, skipping leading spaces. *ok is false if no digit. */
static char *parse_uint(char *p, uint32_t *out, bool *ok)
{
    while (*p == ' ') p++;
    if (*p < '0' || *p > '9') { *ok = false; return p; }
    uint32_t v = 0;
    while (*p >= '0' && *p <= '9') { v = v * 10 + (uint32_t)(*p - '0'); p++; }
    *out = v;
    *ok = true;
    return p;
}

/* Parse a dotted-quad IPv4 address. Returns false on malformed input. */
static bool parse_ip(char **pp, uint8_t ip[4])
{
    char *p = *pp;
    while (*p == ' ') p++;
    for (int i = 0; i < 4; i++) {
        bool ok;
        uint32_t oct;
        p = parse_uint(p, &oct, &ok);
        if (!ok || oct > 255) return false;
        ip[i] = (uint8_t)oct;
        if (i < 3) {
            if (*p != '.') return false;
            p++;
        }
    }
    *pp = p;
    return true;
}

static void print_help(void)
{
    sddf_printf(
        "commands:\n"
        "  start <ip> [port] [dur_s] [streams] [bw_mbps] [len]\n"
        "        run a %s test against <ip>. optional args (left to right):\n"
        "          port      iperf3 server port           (default 5202)\n"
        "          dur_s     test duration in seconds      (default %u)\n"
        "          streams   parallel streams (1..%u)      (default 1)\n"
        "          bw_mbps   rate target, 0 = unlimited    (default 0)\n"
        "          len       UDP payload bytes             (default 1460)\n"
        "  status   show whether a test is running\n"
        "  help     show this message\n"
        "example: start 172.16.0.101 5202 10 4 1000\n",
        PROTO_STR, (unsigned)DEFAULT_DURATION_S, (unsigned)MAX_STREAMS);
}

static void handle_command(char *line)
{
    char *p = line;
    while (*p == ' ') p++;
    if (*p == '\0') return;

    char *rest;
    if ((rest = match_word(p, "help")) || (rest = match_word(p, "?"))) {
        print_help();
    } else if ((rest = match_word(p, "status"))) {
        if (ctrl.test_active && !ctrl.sent_test_end) {
            sddf_printf("a test is running\n");
        } else {
            sddf_printf("idle — %s, network %s\n", PROTO_STR,
                        netif_ready ? "up" : "down");
        }
    } else if ((rest = match_word(p, "start"))) {
        uint8_t ip[4];
        if (!parse_ip(&rest, ip)) {
            sddf_printf("usage: start <ip> [port] [dur_s] [streams] [bw_mbps] [len]\n");
            return;
        }
        uint16_t port = 5202;
        uint32_t dur = DEFAULT_DURATION_S;
        uint8_t streams = 1;
        uint32_t bw = 0;
        uint16_t len = 1460;
        bool ok;
        uint32_t v;
        char *q;
        if ((q = parse_uint(rest, &v, &ok)), ok) { port = (uint16_t)v; rest = q; }
        if ((q = parse_uint(rest, &v, &ok)), ok) { dur = v; rest = q; }
        if ((q = parse_uint(rest, &v, &ok)), ok) { streams = (uint8_t)v; rest = q; }
        if ((q = parse_uint(rest, &v, &ok)), ok) { bw = v; rest = q; }
        if ((q = parse_uint(rest, &v, &ok)), ok) { len = (uint16_t)v; rest = q; }
        if (streams < 1) streams = 1;
        if (streams > MAX_STREAMS) streams = MAX_STREAMS;
        if (len < 1) len = 1;
        if (len > 1460) len = 1460;

        /* Controller: publish the params and poke every peer so they run the
         * same test concurrently (each against base_port + its own client_id).
         * Writes the params first, then bumps `generation` last as the signal. */
        if (multi_config.is_controller && multi_config.num_peers > 0) {
            shared_params->server_ip[0] = ip[0];
            shared_params->server_ip[1] = ip[1];
            shared_params->server_ip[2] = ip[2];
            shared_params->server_ip[3] = ip[3];
            shared_params->base_port = port;
            shared_params->duration_s = dur;
            shared_params->num_streams = streams;
            shared_params->bw_mbps = bw;
            shared_params->payload_len = len;
            __atomic_store_n(&shared_params->generation, ++shared_gen_local, __ATOMIC_RELEASE);
            for (uint8_t pi = 0; pi < multi_config.num_peers; pi++) {
                microkit_notify(multi_config.peer_channels[pi]);
            }
            sddf_printf("[multi] broadcast test to %u peer(s)\n", multi_config.num_peers);
        }

        /* This client targets base_port + its own id (controller id 0 => port). */
        iperf3_begin_test(ip[0], ip[1], ip[2], ip[3],
                          port + app_config.client_id, dur, streams, bw, len);
    } else {
        sddf_printf("unknown command — type 'help'\n");
    }
}

/* Accumulate serial RX into a line buffer; dispatch on CR/LF. */
#define CMD_BUF_SIZE 128
static char cmd_buf[CMD_BUF_SIZE];
static uint32_t cmd_len = 0;

static void serial_rx_poll(void)
{
    char ch;
    while (!serial_dequeue(&serial_rx_queue_handle, &ch)) {
        if (ch == '\r' || ch == '\n') {
            sddf_printf("\n");
            cmd_buf[cmd_len] = '\0';
            handle_command(cmd_buf);
            cmd_len = 0;
            print_prompt();
        } else if (ch == 0x7f || ch == '\b') {      /* DEL / backspace */
            if (cmd_len > 0) {
                cmd_len--;
                sddf_printf("\b \b");
            }
        } else if (cmd_len < CMD_BUF_SIZE - 1) {
            cmd_buf[cmd_len++] = ch;
            sddf_putchar_unbuffered(ch);            /* echo */
        }
    }
}

void netif_status_callback(char *ip_addr)
{
    sddf_printf("DHCP request finished, IP address for netif %s is: %s\n",
                sddf_get_pd_name(), ip_addr);
    netif_ready = true;
    if (multi_config.is_controller) {
        sddf_printf("Ready. Type 'start <server_ip> [opts]' to run an iperf3 %s test "
                    "(or 'help').\n", PROTO_STR);
        print_prompt();
    } else {
        sddf_printf("client %u ready (%s) — waiting for the controller to start a test\n",
                    app_config.client_id, PROTO_STR);
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
    /* RX queue carries keyboard input from serial_virt_rx so a test can be
     * started at runtime (see serial_rx_poll / handle_command). */
    serial_queue_init(&serial_rx_queue_handle, serial_config.rx.queue.vaddr,
                      serial_config.rx.data.size, serial_config.rx.data.vaddr);

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
    } else if (ch == serial_config.rx.id) {
        /* Keyboard input arrived — read commands (start/status/help). */
        serial_rx_poll();
    } else if (!multi_config.is_controller && ch == multi_config.listen_channel) {
        /* Peer client: controller published a test. Run the same params against
         * our own server port (base_port + client_id). Acquire-load pairs with
         * the controller's release-store so the params are visible. */
        uint32_t g = __atomic_load_n(&shared_params->generation, __ATOMIC_ACQUIRE);
        if (g != shared_gen_seen) {
            shared_gen_seen = g;
            iperf3_begin_test(shared_params->server_ip[0], shared_params->server_ip[1],
                              shared_params->server_ip[2], shared_params->server_ip[3],
                              shared_params->base_port + app_config.client_id,
                              shared_params->duration_s, shared_params->num_streams,
                              shared_params->bw_mbps, shared_params->payload_len);
        }
    } else if (ch == serial_config.tx.id) {
        /* TX free notification — nothing to do */
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
