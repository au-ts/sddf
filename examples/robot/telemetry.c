#include "include/telemetry/telemetry.h"
#include "include/motor/encoder.h"
#include "include/gpio_common/gpio_common.h"

#define DEBUG_LOG

#ifdef DEBUG_LOG
#define LOG_TELEM(...) do{ sddf_printf("TELEM|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_TELEM_ERR(...) do{ sddf_printf("TELEM|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_TELEM(...) do{}while(0)
#define LOG_TELEM_ERR(...) do{}while(0)
#endif

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
    LOG_TELEM("NOTIFICATION FROM %d\n", ch);
    if (ch == timer_channel) {
        LOG_TELEM("TEST TIMER\n");

        // calculate revolutions per second
        double wheel_ppr = PPR * REDUCTION;
        double rps = encoder_count / wheel_ppr;
        encoder_count = 0;
        
        LOG_TELEM("%f\n", rps);
        sddf_timer_set_timeout(timer_channel, 10*NS_IN_US);
        co_switch(t_main);
    }
}

void telemetry_main(void) {
    LOG_TELEM("main\n");

    // start timer to calculate wheel speeds every second
    sddf_timer_set_timeout(timer_channel, 10*NS_IN_US);
    detect_encoder_rising_edge(gpio_channel_encoder_a, gpio_channel_encoder_b);
}

void init(void) {
    timer_channel = timer_config.driver_id;

    gpio_channel_encoder_a = gpio_config.driver_channel_ids[6];
    gpio_channel_encoder_b = gpio_config.driver_channel_ids[7];

    encoder_init(gpio_channel_encoder_a, gpio_channel_encoder_b);

    LOG_TELEM("Init\n");

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, telemetry_main);
    
    co_switch(t_main);
}
