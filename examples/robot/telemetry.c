#include <microkit.h>
#include <sddf/util/printf.h>
#include <os/sddf.h>
#include <stdint.h>
#include <sddf/gpio/client.h>
#include <sddf/gpio/config.h>
#include <sddf/gpio/protocol.h>
#include "include/motor/encoder.h"
#include "include/gpio_common/gpio_common.h"

__attribute__((__section__(".gpio_telemetry_config"))) gpio_client_config_t gpio_config;

sddf_channel gpio_channel_encoder_a = 0;
sddf_channel gpio_channel_encoder_b = 0;

// djb2 hash: http://www.cse.yorku.ca/~oz/hash.html
unsigned long generate_hash(char str[])
{
    unsigned long hash = 5381;
    int c;

    while (c = *str++) {
        hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
    }

    return hash;
}

void notified(sddf_channel ch) {
    sddf_printf("Unexpected channel call\n");
}

void init(void) {
    gpio_channel_encoder_a = gpio_config.driver_channel_ids[6];
    gpio_channel_encoder_b = gpio_config.driver_channel_ids[7];
    encoder_init(gpio_channel_encoder_a, gpio_channel_encoder_b);

    detect_encoder_rising_edge(gpio_channel_encoder_a, gpio_channel_encoder_b);
}
