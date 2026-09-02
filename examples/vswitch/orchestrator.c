/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/network/config.h>
#include <sddf/network/vswitch.h>
#include <sddf/serial/config.h>
#include <sddf/serial/queue.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/util/printf.h>

/* Allow DHCP and client IP discovery to complete before the first ACL change. */
#define ACL_UPDATE_INTERVAL_NS (5 * NS_IN_S)
#define ACL_TEST_NUM_CLIENTS 2
#define CLIENT0_CHANNEL 60
#define CLIENT1_CHANNEL 61

__attribute__((__section__(".net_vswitch_orchestrator_config"))) net_vswitch_orchestrator_config_t vswitch_config;
__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

static serial_queue_handle_t serial_tx_queue_handle;
static bool acl_enabled = true;
static bool clients_ready[ACL_TEST_NUM_CLIENTS];

static bool all_clients_ready()
{
    for (uint8_t i = 0; i < ACL_TEST_NUM_CLIENTS; i++) {
        if (!clients_ready[i]) {
            return false;
        }
    }

    return true;
}

/* Wait for Client 0 and 1 to claim ready for ACL tests */
static bool handle_client_ready(sddf_channel ch)
{
    if (ch == CLIENT0_CHANNEL) {
        clients_ready[0] = true;
        sddf_printf("vSwitch orchestrator: client 0 completed neighbour discovery\n");
        return true;
    }
    if (ch == CLIENT1_CHANNEL) {
        clients_ready[1] = true;
        sddf_printf("vSwitch orchestrator: client 1 completed neighbour discovery\n");
        return true;
    }

    return false;
}

/* Update both directions of the ACL between two vSwitch ports. */
static void set_acl(uint8_t port0, uint8_t port1, bool enabled)
{
    sddf_set_mr(VSWITCH_ACL_PORT0, port0);
    sddf_set_mr(VSWITCH_ACL_PORT1, port1);
    sddf_set_mr(VSWITCH_ACL_VALUE, enabled);
    sddf_ppcall(vswitch_config.vswitch_id, seL4_MessageInfo_new(VSWITCH_SET_ACL, 0, 0, VSWITCH_ACL_NUM_ARGS));

    vswitch_err_t err = sddf_get_mr(VSWITCH_ACL_RET_ERR);
    if (err == VSWITCH_ERR_OKAY) {
        sddf_printf("vSwitch ACL: port %u <-> port %u is %s\n", port0, port1, enabled ? "enabled" : "disabled");
    } else {
        sddf_printf("vSwitch ACL update failed: %u\n", err);
    }
}

void init(void)
{
    assert(net_config_check_magic(&vswitch_config));
    assert(serial_config_check_magic(&serial_config));
    assert(timer_config_check_magic(&timer_config));

    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

    sddf_printf("vSwitch orchestrator: toggling ACL 0 <-> 1 every 5 seconds\n");
    sddf_timer_set_timeout(timer_config.driver_id, ACL_UPDATE_INTERVAL_NS);
}

void notified(sddf_channel ch)
{
    if (ch == timer_config.driver_id) {
        if (all_clients_ready()) {
            acl_enabled = !acl_enabled;
            set_acl(0, 1, acl_enabled);
        }
        sddf_timer_set_timeout(timer_config.driver_id, ACL_UPDATE_INTERVAL_NS);
    } else if (ch == serial_config.tx.id) {
        // Nothing to do
    } else if (!handle_client_ready(ch)) {
        sddf_dprintf("vSwitch orchestrator: unexpected notification %u\n", ch);
    }
}
