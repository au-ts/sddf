#include "include/gpio_common/gpio_common.h"

void gpio_init(int gpio_ch, int direction) {
    int ret = 0;

    if (direction == GPIO_DIRECTION_INPUT) {
        // set gpio to initial value of zero
        ret = sddf_gpio_direction_output(gpio_ch, GPIO_LOW);
        if (ret < 0) {
            LOG_CLIENT_ERR("Failed to set direction to output. Error code : %d!\n", ret);
            assert(false);
        }
    }
    else if (direction == GPIO_DIRECTION_OUTPUT) {
        ret = sddf_gpio_direction_input(gpio_ch);
        if (ret < 0) {
            LOG_CLIENT_ERR("Failed to set direction to input. Error code : %d!\n", ret);
            assert(false);
        }
    }
}

void digital_write(int gpio_ch, int value) {
    int ret = sddf_gpio_set(gpio_ch, value);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set value. Error code : %d!\n", ret);
        assert(false);
    }
}