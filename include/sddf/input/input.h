#pragma once

#include <stdint.h>

enum input_event_type {
    INPUT_EVENT_TYPE_KEY,
    INPUT_EVENT_TYPE_MOUSE,
};

typedef struct input_event {
    input_event_type type;
} input_event_t;
