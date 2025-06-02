#include <microkit.h>
#include <sddf/spi/config.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>

__attribute((__section__(".spi_driver_config"))) spi_driver_config_t config;

__attribute((__section__(".device_resources"))) device_resources_t device_resources;

void notified(microkit_channel ch) {
    sddf_printf("driver: notified on channel %d\n", ch);
};

void init() {
    microkit_dbg_puts("hello!\n");
}
