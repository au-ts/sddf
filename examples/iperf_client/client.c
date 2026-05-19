#include "lwip/apps/lwiperf.h"
#include "lwip/ip_addr.h"

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
#include "lwip/pbuf.h"



__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

__attribute__((__section__(".net_client_config"))) net_client_config_t net_config;

__attribute__((__section__(".benchmark_client_config"))) benchmark_client_config_t benchmark_config;

__attribute__((__section__(".lib_sddf_lwip_config"))) lib_sddf_lwip_config_t lib_sddf_lwip_config;

serial_queue_handle_t serial_tx_queue_handle;

net_queue_handle_t net_rx_handle;
net_queue_handle_t net_tx_handle;

static bool dhcp_ready = false;
static bool iperf_started = false;

void netif_status_callback(char *ip_addr)
{
    dhcp_ready = true;
    sddf_printf("DHCP finished, IP address: %s\n", ip_addr);
}

static void iperf_report(void *arg, enum lwiperf_report_type report_type,
  const ip_addr_t* local_addr, u16_t local_port, const ip_addr_t* remote_addr, u16_t remote_port,
  u32_t bytes_transferred, u32_t ms_duration, u32_t bandwidth_kbitpsec) {
    (void)arg;
    (void)local_addr;
    (void)remote_addr;

    sddf_printf("[lwiperf] type=%d bytes=%u dur_ms=%u bw_kbitps=%u local_port=%u remote_port=%u\n",
          (int)report_type,
          (unsigned)bytes_transferred,
          (unsigned)ms_duration,
          (unsigned)bandwidth_kbitpsec,
          (unsigned)local_port,
          (unsigned)remote_port);
}

static void try_start_iperf(void)
{
    if (!dhcp_ready || iperf_started) {
        return;
    }

    ip_addr_t server_addr;
    IP_ADDR4(&server_addr, 10, 0, 2, 2);

    lwiperf_start_tcp_client_default(&server_addr, iperf_report, NULL);
    iperf_started = true;

    sddf_printf("lwiperf client started\n");
}

#define LWIP_TICK_MS 10


void set_timeout(void)
{
    sddf_timer_set_timeout(timer_config.driver_id, LWIP_TICK_MS * NS_IN_MS);
}

void init(void) {
  serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
  serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

  net_queue_init(&net_rx_handle, net_config.rx.free_queue.vaddr, net_config.rx.active_queue.vaddr,
                  net_config.rx.num_buffers);
  net_queue_init(&net_tx_handle, net_config.tx.free_queue.vaddr, net_config.tx.active_queue.vaddr,
                  net_config.tx.num_buffers);
  net_buffers_init(&net_tx_handle, 0);

  sddf_lwip_init(&lib_sddf_lwip_config, &net_config, &timer_config, net_rx_handle, net_tx_handle, NULL, NULL,
                  netif_status_callback, NULL, NULL, NULL);
  // ip_addr_t server_addr;
  // IP_ADDR4(&server_addr, 10, 0, 2, 2);
  // lwiperf_start_tcp_client_default(&server_addr, iperf_report, NULL);
  set_timeout();
}

void notified(sddf_channel ch) {
  if (ch == net_config.rx.id) {
    sddf_lwip_process_rx();
  } else if (ch == timer_config.driver_id) {
    sddf_lwip_process_timeout();
    try_start_iperf();
    set_timeout();
  } else if (ch == serial_config.tx.id || ch == net_config.tx.id) {
      // Nothing to do
  } else {
    sddf_dprintf("LWIP|LOG: received notification on unexpected channel: %u\n", ch);
  }

  sddf_lwip_maybe_notify();
}


