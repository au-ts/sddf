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

#include "iperf3_util.h"

__attribute__((__section__(".iperf3_app_config"))) iperf3_app_config_t app_config;

/* Multi-client coordination (WIP) */
__attribute__((__section__(".iperf3_multi_config"))) iperf3_multi_config_t multi_config;
static volatile iperf3_shared_params_t *shared_params =
    (volatile iperf3_shared_params_t *)IPERF3_SHARED_PARAMS_VADDR;
static uint32_t shared_gen_local;
static uint32_t shared_gen_seen;


static uint64_t bench_core_start[CONFIG_MAX_NUM_NODES];
static uint64_t bench_idle_start[CONFIG_MAX_NUM_NODES];
static bool bench_snapshotted;
static bool bench_reported;

/* TX packet count over the measurement window from lwIP stats */
static uint32_t pkts_segs_start;
static bool pkts_snapshotted, pkts_reported;

// configs to be injected into elf
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

// make cookie logic
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

#define DEFAULT_IS_UDP false   /* default protocol is TCP */

static const char *proto_str(bool is_udp) { return is_udp ? "UDP" : "TCP"; }
static uint32_t default_duration_s(bool is_udp) { return is_udp ? 5 : 10; }

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

/* Open and initialises control connection and kick off a test against a server */
static void iperf3_begin_test(uint8_t a, uint8_t b, uint8_t c, uint8_t d,
                              uint16_t port, uint32_t duration_s,
                              uint8_t num_streams, uint32_t bw_mbps,
                              uint16_t payload_len, bool is_udp, bool is_reverse, bool is_bidirectional,
                              uint32_t blocks)
{
    if (!netif_ready) {
        sddf_printf("network is not up yet - wait for the DHCP message\n");
        return;
    }
    if (ctrl.test_active && !ctrl.sent_test_end) {
        sddf_printf("a test is already running - wait for it to finish\n");
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
    ctrl.is_udp = is_udp;
    ctrl.duration_s = duration_s;
    ctrl.num_streams = num_streams;
    ctrl.target_bw_mbps = bw_mbps;
    ctrl.target_blocks = blocks;
    ctrl.payload_len = payload_len;
    ctrl.omit_s = is_udp ? 0 : 5;
    ctrl.is_reverse = is_reverse;
    ctrl.is_bidirectional = is_bidirectional;


    bench_snapshotted = bench_reported = false;
    pkts_snapshotted = pkts_reported = false;

    tcp_arg(pcb, &ctrl);
    make_cookie(ctrl.cookie);

    sddf_printf("Starting iperf3 (%s) -> %u.%u.%u.%u:%u  dur=%us streams=%u bw=%uM len=%u, reverse=%s, bidirectional=%s\n",
                proto_str(is_udp), a, b, c, d, port, duration_s, num_streams, bw_mbps, payload_len, is_reverse ? "true" : "false", is_bidirectional ? "true" : "false");

    error = tcp_connect(pcb, &server_addr, port, iperf_ctrl_connect);
    if (error) {
        sddf_printf("Failed to connect TCP control socket: %s\n", lwip_strerr(error));
        return;
    }
}

/* If line matches word return a
 * pointer just past the word otherwise NULL.
 */
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

/* Parse a decimal uint. *ok is false if no digit. */
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
        "  SERVER: \n"
        "  start server [port]\n"
        "  CLIENT:\n"
        "  start [tcp|udp] <ip> [port] [dur_s] [streams] [bw_mbps] [len]\n"
        "        run a test against <ip>. optional args (left to right):\n"
        "          tcp|udp   protocol                       (default udp)\n"
        "          port      iperf3 server port             (default 5202)\n"
        "          dur_s     test duration in seconds       (default 10 tcp / 5 udp)\n"
        "          streams   parallel streams (1..%u)       (default 1)\n"
        "          bw_mbps   rate target, 0 = unlimited     (default 0)\n"
        "          len       UDP payload bytes              (default 1460, udp only)\n"
        "          reverse   server sends data              (default false)\n"
        "          bidirectional   server sends data        (default false)\n"
        "  status   show whether a test is running\n"
        "  help     show this message\n"
        "example: start tcp 172.16.0.101 5202 10 1 1000 bidirectional\n",
        "example: start server 5202\n",
        proto_str(DEFAULT_IS_UDP), MAX_STREAMS);
}

// start udp 172.16.0.101 5202 10 1 1000 true
static void handle_command(char *line)
{
    char *p = line;
    while (*p == ' ') p++;
    if (*p == '\0') return;

    char *rest;
    // help or ? or start match
    if ((rest = match_word(p, "help")) || (rest = match_word(p, "?"))) {
        print_help();
    } else if ((rest = match_word(p, "status"))) {
        if (ctrl.test_active && !ctrl.sent_test_end) {
            sddf_printf("a test is running (%s)\n", proto_str(ctrl.is_udp));
        } else {
            sddf_printf("idle - network %s\n", netif_ready ? "up" : "down");
        }
    } else if ((rest = match_word(p, "start"))) {
        bool is_udp = DEFAULT_IS_UDP;
        char *tok = rest;
        while (*tok == ' ') tok++;
        char role = 'c';
        char *after;

        uint16_t port = 5202;
        uint32_t v;
        bool ok;
        
        char *q;
        // protocol or server
        if ((after = match_word(tok, "udp"))) { is_udp = true; rest = after; }
        else if ((after = match_word(tok, "tcp"))) { is_udp = false; rest = after; }
        else if (after = match_word(tok, "server")) { 
            role = 's', rest = after;
            
            if ((q = parse_uint(rest, &v, &ok)), ok) { port = (uint16_t)v; rest = q; }
            iperf3_server_listen(&ctrl, port);
            return;

        }

        uint8_t ip[4];
        if (!parse_ip(&rest, ip)) {
            sddf_printf("usage: start [tcp|udp] <ip> [port] [dur_s] [streams] [bw_mbps] [len] [reverse]/[bidirectional]\n");
            return;
        }
        uint32_t dur = default_duration_s(is_udp);
        uint8_t streams = 1;
        uint32_t bw = 0;
        uint16_t len = 1460;
        uint32_t blocks = 0;
        bool reverse = false;
        bool is_bidirectional = false;
        
        if ((q = parse_uint(rest, &v, &ok)), ok) { port = (uint16_t)v; rest = q; }
        if ((q = parse_uint(rest, &v, &ok)), ok) { dur = v; rest = q; }
        if ((q = parse_uint(rest, &v, &ok)), ok) { streams = (uint8_t)v; rest = q; }
        if ((q = parse_uint(rest, &v, &ok)), ok) { bw = v; rest = q; }
        if ((q = parse_uint(rest, &v, &ok)), ok) { len = (uint16_t)v; rest = q; }

        
        /* "blocks N" replaces the duration: stop after N blocks of <len>. */
        while (*rest == ' ') rest++;
        if ((q = match_word(rest, "blocks"))) {
            rest = q;
            if ((q = parse_uint(rest, &v, &ok)), ok) { blocks = v; rest = q; }
            else sddf_printf("blocks needs a count!\n");
        }

        while (*rest == ' ') rest++;
        if ((q = match_word(rest, "reverse"))) { reverse = true; rest = q; }
        else if (q = match_word(rest, "bidirectional")) {is_bidirectional = true, rest = q;}

        if (streams < 1) streams = 1;
        if (streams > MAX_STREAMS) streams = MAX_STREAMS;
        if (len < 1) len = 1;
        if (len > 1460) len = 1460;

        /* Controller publish the params and notifies every peer */
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
            shared_params->is_udp = is_udp ? 1 : 0;
            shared_params->is_reverse = reverse ? 1 : 0;
            shared_params->is_bidirectional = is_bidirectional ? 1 : 0;
            shared_params->blocks = blocks;
            __atomic_store_n(&shared_params->generation, ++shared_gen_local, __ATOMIC_RELEASE);
            for (uint8_t pi = 0; pi < multi_config.num_peers; pi++) {
                microkit_notify(multi_config.peer_channels[pi]);
            }
            sddf_printf("[multi] broadcast test to %u peer(s)\n", multi_config.num_peers);
        }

        iperf3_begin_test(ip[0], ip[1], ip[2], ip[3],
                          port + app_config.client_id, dur, streams, bw, len, is_udp, reverse,
                          is_bidirectional, blocks);
    } else {
        sddf_printf("unknown command - type 'help'\n");
    }
}

/* Accumulate serial RX into a line buffer finish on CR/LF. */
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
        } else if (ch == 0x7f || ch == '\b') {
            if (cmd_len > 0) {
                cmd_len--;
                serial_write_unbuffered("\b \b");
            }
        } else if (cmd_len < CMD_BUF_SIZE - 1) {
            cmd_buf[cmd_len++] = ch;
            sddf_putchar_unbuffered(ch);
        }
    }
}

void netif_status_callback(char *ip_addr)
{
    sddf_printf("DHCP request finished, IP address for netif %s is: %s\n",
                sddf_get_pd_name(), ip_addr);
    netif_ready = true;
    if (multi_config.is_controller) {
        sddf_printf("Ready. Type 'start [tcp|udp] <server_ip> [opts]' to run an iperf3 test "
                    "(or 'help').\n");
        print_prompt();
    } else {
        sddf_printf("client %u ready - waiting for the controller to start a test\n",
                    app_config.client_id);
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
    setup_utilization_socket(&benchmark_config);

    sddf_lwip_maybe_notify();
}

void notified(sddf_channel ch)
{
    if (ch == net_config.rx.id) {
        // lwip process receive
        sddf_lwip_process_rx();
    } else if (ch == timer_config.driver_id) {
        /** LWIP processes timeout.
         * check timers
         * 
         */
        sddf_lwip_process_timeout();
  
        uint32_t now_ms = sddf_timer_time_now(timer_config.driver_id) / 1000000;
        if (ctrl.is_udp) {
            for (int s = 0; s < MAX_STREAMS; s++) {
                ctrl.udp_streams[s].packets_this_tick = 0;
            }
            iperf3_on_timer_tick(&ctrl, now_ms);
            if (ctrl.test_active && !ctrl.test_done) {
                net_request_signal_free(&net_tx_handle);
            }
        } else {
       
            iperf3_tcp_check_deadline(&ctrl, now_ms);
            for (int s = 0; s < MAX_STREAMS; s++) {
                if (ctrl.streams[s].pcb != NULL && ctrl.streams[s].phase == SEND_PAYLOAD) {
                    ctrl.streams[s].bytes_this_tick = 0;
                    iperf3_stream_maybe_tx(&ctrl.streams[s]);
                }
            }
        }
        set_timeout();
    } else if (ch == serial_config.rx.id) {
        /* Keyboard input arrived - read commands (start/status/help). */
        serial_rx_poll();
    } else if (!multi_config.is_controller && ch == multi_config.listen_channel) {
        /* Peer client (used for multicore) */
        uint32_t g = __atomic_load_n(&shared_params->generation, __ATOMIC_ACQUIRE);
        if (g != shared_gen_seen) {
            shared_gen_seen = g;
            iperf3_begin_test(shared_params->server_ip[0], shared_params->server_ip[1],
                              shared_params->server_ip[2], shared_params->server_ip[3],
                              shared_params->base_port + app_config.client_id,
                              shared_params->duration_s, shared_params->num_streams,
                              shared_params->bw_mbps, shared_params->payload_len,
                              shared_params->is_udp != 0, shared_params->is_reverse,
                              shared_params->is_bidirectional, shared_params->blocks);
        }
    } else if (ch == serial_config.tx.id) {
        /* TX free notification - nothing to do */
    } else if (ch == net_config.tx.id) {
        /* TX buffers freed UDP continues pumping*/
        if (ctrl.is_udp) {
            uint32_t now_ms = sddf_timer_time_now(timer_config.driver_id) / 1000000;
            iperf3_on_timer_tick(&ctrl, now_ms);
            if (ctrl.test_active && !ctrl.test_done) {
                net_request_signal_free(&net_tx_handle);
            }
        }
    } else {
        sddf_dprintf("LWIP|LOG: received notification on unexpected channel: %u\n", ch);
    }

    if (!ctrl.is_udp && ctrl.test_active && !ctrl.sent_test_end) {
        static uint32_t deadline_throttle = 0;
        if ((deadline_throttle++ & 0x3F) == 0) {
            uint32_t now_ms = sddf_timer_time_now(timer_config.driver_id) / 1000000;
            iperf3_tcp_check_deadline(&ctrl, now_ms);
        }
    }

    sddf_lwip_maybe_notify();

    /* re-arm for the next test */
    if (!ctrl.test_active && bench_reported) {
        bench_snapshotted = bench_reported = false;
        pkts_snapshotted = pkts_reported = false;
    }

    /* Snapshot every active core's idle-PD counters */
    if (ctrl.test_active && !ctrl.omitting && !bench_snapshotted && benchmark_config.num_cores > 0) {
        for (uint8_t c = 0; c < benchmark_config.num_cores; c++) {
            struct bench *b = (struct bench *)benchmark_config.core_ccounts[c];
            bench_core_start[c] = __atomic_load_n(&b->core_ccount, __ATOMIC_RELAXED);
            bench_idle_start[c] = __atomic_load_n(&b->idle_ccount, __ATOMIC_RELAXED);
        }
        bench_snapshotted = true;
        microkit_notify(benchmark_config.start_ch);
    }

    /* TX packet count */
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

                ctrl.cpu_util_percent = util;
            } else {
                sddf_printf("[cpu_util] no data - build with MICROKIT_CONFIG=benchmark/smp-benchmark\n");
            }
        }

        if (!ctrl.is_udp) {
            uint32_t mn, mean, mx, sd; uint64_t n;
            iperf3_tcp_rtt_aggregate(&ctrl, &mn, &mean, &mx, &sd, &n);
            sddf_printf("[rtt] min=%u mean=%u max=%u sd=%u us (n=%llu)\n",
                        mn, mean, mx, sd, (unsigned long long)n);
        }

        if (ctrl.is_reverse) {
            if (ctrl.is_udp) {
                uint64_t bytes = 0, packets = 0;
                int lost = 0;
                double jitter_ms = 0.0;
                for (uint8_t s = 0; s < ctrl.num_streams; s++) {
                    iperf3_udp_stream_t *us = &ctrl.udp_streams[s];
                    bytes += us->rx_bytes;
                    packets += us->rx_packets;
                    if (us->rx_have_first) {
                        int l = (int)(us->rx_last_seq - us->rx_first_seq) + 1 - (int)us->rx_packets;
                        if (l > 0) lost += l;
                    }
                    double jm = us->rx_jitter * 1000.0;   /* seconds -> ms */
                    if (jm > jitter_ms) jitter_ms = jm;
                }
                sddf_printf("[rev] udp rx_bytes=%llu packets=%llu lost=%d jitter_ms=%.4f\n",
                            (unsigned long long)bytes, (unsigned long long)packets, lost, jitter_ms);
            } else {
                uint64_t bytes = 0;
                for (uint8_t s = 0; s < ctrl.num_streams; s++) {
                    bytes += ctrl.streams[s].rx_bytes;
                }
                sddf_printf("[rev] tcp rx_bytes=%llu\n", (unsigned long long)bytes);
            }
        }
        sddf_printf("MQ_EXIT\n");
    }
}