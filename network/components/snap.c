#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <microkit.h>
#include <sddf/network/shared_ringbuffer.h>
#include <sddf/network/constants.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/timer/client.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#define START_CH    0
#define STOP_CH     1
#define TIMER_CH    2

#define NUM_SAMPLE  4096
// #define INTERVAL_S  5
#define INTERVAL_S  1

/* Ring buffer regions */
uintptr_t rx_free_cli0 = 0x2000000;
uintptr_t rx_used_cli0 = 0x2200000;
uintptr_t tx_free_cli0 = 0x2400000;
uintptr_t tx_used_cli0 = 0x2600000;

uintptr_t rx_free_drv = 0x2800000;
uintptr_t rx_used_drv = 0x2a00000;
uintptr_t tx_free_drv = 0x2c00000;
uintptr_t tx_used_drv = 0x2e00000;

typedef struct state {
    ring_handle_t rx_ring_cli0;
    ring_handle_t tx_ring_cli0;
    ring_handle_t rx_ring_drv;
    ring_handle_t tx_ring_drv;
} state_t;

state_t state;

typedef struct result {
    uint32_t idx;

    uint32_t rx_free_ring_cli0[NUM_SAMPLE];
    uint32_t rx_used_ring_cli0[NUM_SAMPLE];

    uint32_t tx_free_ring_cli0[NUM_SAMPLE];
    uint32_t tx_used_ring_cli0[NUM_SAMPLE];

    uint32_t rx_free_ring_drv[NUM_SAMPLE];
    uint32_t rx_used_ring_drv[NUM_SAMPLE];
    
    uint32_t tx_free_ring_drv[NUM_SAMPLE];
    uint32_t tx_used_ring_drv[NUM_SAMPLE];
} result_t;

result_t res;

void init(void)
{
    // printf("snap init\n");
    // ring_init(&state.rx_ring_cli0, (ring_buffer_t *) rx_free_cli0, (ring_buffer_t *) rx_used_cli0, RX_RING_SIZE_CLI0);
    // ring_init(&state.tx_ring_cli0, (ring_buffer_t *) tx_free_cli0, (ring_buffer_t *) tx_used_cli0, TX_RING_SIZE_CLI0);

    // ring_init(&state.rx_ring_drv, (ring_buffer_t *) rx_free_drv, (ring_buffer_t *) rx_used_drv, RX_RING_SIZE_DRIV);
    // ring_init(&state.tx_ring_drv, (ring_buffer_t *) tx_free_drv, (ring_buffer_t *) tx_used_drv, TX_RING_SIZE_DRIV);
}

void reset(void) {
    res.idx = 0;
}

void snapshot(void) {
    if (res.idx == NUM_SAMPLE) {
        return;
    }
    res.rx_free_ring_cli0[res.idx] = ring_size(state.rx_ring_cli0.free_ring);
    res.rx_used_ring_cli0[res.idx] = ring_size(state.rx_ring_cli0.used_ring);

    res.tx_free_ring_cli0[res.idx] = ring_size(state.tx_ring_cli0.free_ring);
    res.tx_used_ring_cli0[res.idx] = ring_size(state.tx_ring_cli0.used_ring);

    res.rx_free_ring_drv[res.idx] = ring_size(state.rx_ring_drv.free_ring);
    res.rx_used_ring_drv[res.idx] = ring_size(state.rx_ring_drv.used_ring);

    res.tx_free_ring_drv[res.idx] = ring_size(state.tx_ring_drv.free_ring);
    res.tx_used_ring_drv[res.idx] = ring_size(state.tx_ring_drv.used_ring);

    res.idx++;
}

void print_result(void) {
    printf("client0 RX free,client0 RX used,client0 TX free,client0 TX used,driver RX free,driver RX used,driver TX free,driver TX used\n");
    for (uint32_t i = 0; i <= res.idx; i++) {
        printf("%d,%d,%d,%d,%d,%d,%d,%d,%d\n", 
               i * INTERVAL_S,
               res.rx_free_ring_cli0[i], res.rx_used_ring_cli0[i],
               res.tx_free_ring_cli0[i], res.tx_used_ring_cli0[i],
               res.rx_free_ring_drv[i], res.rx_used_ring_drv[i],
               res.tx_free_ring_drv[i], res.tx_used_ring_drv[i]);
    }
}

void notified(microkit_channel ch)
{
    switch(ch) {
        case START_CH:
            // reset();
            // snapshot();
            // sddf_timer_set_timeout(TIMER_CH, INTERVAL_S * 1000000000lu);
            break;

        case STOP_CH:
            // print_result();
            break;

        case TIMER_CH:
            // snapshot();
            // sleep for INTERVAL_S seconds.
            // sddf_timer_set_timeout(TIMER_CH, INTERVAL_S * 1000000000lu);
            break;

        default:
            printf("SNAP|LOG: received notification on unexpected channel: %lu\n", ch);
            break;
    }
}