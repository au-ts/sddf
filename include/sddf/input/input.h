#pragma once

#include <stdint.h>
#include <stddef.h>

struct virtio_input_event {
    uint16_t type;
    uint16_t code;
    uint32_t value;
};

struct input_event_queue {
    size_t n;
    struct virtio_input_event events[];
};
