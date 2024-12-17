#include <microkit.h>

#define BENCHMARK_MAX_CHILDREN 64 // TODO: is there an upper bound?

typedef struct benchmark_child_config {
    char name[MICROKIT_PD_NAME_LENGTH];
    uint8_t child_id;
} benchmark_child_config_t;

typedef struct benchmark_config {
    uint8_t start_channel;
    uint8_t stop_channel;
    uint8_t init_channel;
    uint8_t num_children;
    benchmark_child_config_t children[BENCHMARK_MAX_CHILDREN];
} benchmark_config_t;

typedef struct benchmark_idle_config {
    void *cycle_counters;
    uint8_t init_channel;
} benchmark_idle_config_t;

typedef struct benchmark_client_config {
    void *cycle_counters;
    uint8_t start_channel;
    uint8_t stop_channel;
} benchmark_client_config_t;
