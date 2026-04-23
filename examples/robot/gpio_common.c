#include "include/gpio_common/gpio_common.h"

#define DEBUG_LOG

#ifdef DEBUG_LOG
#define LOG_GPIO(...) do{ sddf_printf("GPIO COMMON|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_GPIO_ERR(...) do{ sddf_printf("GPIO COMMON|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_GPIO(...) do{}while(0)
#define LOG_GPIO_ERR(...) do{}while(0)
#endif

void gpio_init(int gpio_ch, int direction, int irq) {
    sddf_printf("GPIO INIT called\n");    
    int ret = 0;

    if (direction == GPIO_DIRECTION_OUTPUT) {
        // set gpio to initial value of zero
        LOG_GPIO("Setting direction of %d to output\n", gpio_ch);
        ret = sddf_gpio_direction_output(gpio_ch, GPIO_LOW);
        if (ret < 0) {
            LOG_GPIO_ERR("Failed to set direction to output. Error code : %d!\n", ret);
            assert(false);
        }
    }
    else if (direction == GPIO_DIRECTION_INPUT) {
        ret = sddf_gpio_direction_input(gpio_ch);
        LOG_GPIO("Setting direction of %d to input\n", gpio_ch);

        if (ret < 0) {
            LOG_GPIO_ERR("Failed to set direction to input. Error code : %d!\n", ret);
            assert(false);
        }
    }

    if (irq != SDDF_IRQ_TYPE_NONE) {
        ret = sddf_gpio_irq_set_type(gpio_ch, irq);
        if (ret < 0) {
            LOG_GPIO_ERR("Failed to set IRQ type. Error code : %d!\n", ret);
            assert(false);
        }

        ret = sddf_gpio_irq_enable(gpio_ch);
        if (ret < 0) {
            LOG_GPIO_ERR("Failed to enable IRQ. Error code : %d!\n", ret);
            assert(false);
        }
        LOG_GPIO("Enabling IRQ");
    }
}

void digital_write(int gpio_ch, int value) {
    int ret = sddf_gpio_set(gpio_ch, value);
    if (ret < 0) {
        LOG_GPIO_ERR("Failed to set value. Error code : %d!\n", ret);
        assert(false);
    }
}

int digital_read(int gpio_ch) {
    int value_received = sddf_gpio_get(gpio_ch);
    if (value_received < 0) {
        LOG_GPIO_ERR("Failed to get value. Error code : %d!\n", value_received);
        assert(false);
    }

    return value_received;
}
