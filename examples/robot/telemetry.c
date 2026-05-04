#include "include/telemetry/telemetry.h"
#include "include/motor/encoder.h"
#include "include/gpio_common/gpio_common.h"

#define STACK_SIZE (4096)

__attribute__((__section__(".gpio_telemetry_config"))) gpio_client_config_t gpio_config;
__attribute__((__section__(".timer_telemetry_config"))) timer_client_config_t timer_config;

static char t_client_main_stack[STACK_SIZE];

cothread_t t_event;
cothread_t t_main;

sddf_channel gpio_channel_encoder_a = 0;
sddf_channel gpio_channel_encoder_b = 0;
sddf_channel timer_channel = 0;

void notified(sddf_channel ch) {
    if (ch == timer_channel) {
        // calculate revolutions per second
        double wheel_ppr = PPR * REDUCTION;
        double rps = encoder_count / (PPR);
        encoder_count = 0;
        
        sddf_timer_set_timeout(timer_channel, NS_IN_S);
        co_switch(t_main);
    }
}

void telemetry_main(void) {
    // start timer to calculate wheel speeds every second
    sddf_timer_set_timeout(timer_channel, NS_IN_S);
    detect_encoder_rising_edge(gpio_channel_encoder_a, gpio_channel_encoder_b);
}

void init(void) {
    timer_channel = timer_config.driver_id;

    gpio_channel_encoder_a = gpio_config.driver_channel_ids[6];
    gpio_channel_encoder_b = gpio_config.driver_channel_ids[7];

    encoder_init(gpio_channel_encoder_a, gpio_channel_encoder_b);

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, telemetry_main);
    
    co_switch(t_main);
}
