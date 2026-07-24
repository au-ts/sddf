#pragma once

#include <stdint.h>

/* Per-client identity injected into the .iperf3_app_config ELF section. The
 * server endpoint is selected at runtime by the controller's start command. */
typedef struct iperf3_app_config {
    uint8_t client_id;      /* 0, 1, ... for logging and base_port offset */
} iperf3_app_config_t;
