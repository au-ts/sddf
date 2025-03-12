/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/serial/queue.h>
#include <sddf/util/printf.h>

#define FLUSH_CHAR '\n'

static microkit_channel tx_ch;
static serial_queue_handle_t *tx_queue_handle;

static uint32_t length;

/* Ensure to call serial_putchar_init during initialisation. Multiplexes output based on \n or when buffer is full. */
void _sddf_putchar(char character)
{
    if (length >= tx_queue_handle->capacity - 1) {
        return;
    }

    uint32_t l = tx_queue_handle->queue->tail + length;
    if (character == '\n') {
        serial_enqueue_local(tx_queue_handle, &l, '\r');
        length += 1;
    }
    serial_enqueue_local(tx_queue_handle, &l, character);
    length +=1;

    /* Make changes visible to virtualiser if character is flush or if queue is now filled */
    if (length == tx_queue_handle->capacity || length == tx_queue_handle->capacity - 1
        || character == FLUSH_CHAR) {
        serial_update_shared_tail(tx_queue_handle, l);
        microkit_notify(tx_ch);
        length = 0;
    }
}

void sddf_putchar_unbuffered(char character)
{
    /* if (serial_queue_full(tx_queue_handle, local_tail)) { */
    /*     return; */
    /* } */

    /* serial_enqueue_local(tx_queue_handle, &local_tail, character); */
    /* serial_update_shared_tail(tx_queue_handle, local_tail); */
    /* microkit_notify(tx_ch); */
}

/* Initialise the serial putchar library. */
void serial_putchar_init(microkit_channel serial_tx_ch, serial_queue_handle_t *serial_tx_queue_handle)
{
    tx_ch = serial_tx_ch;
    tx_queue_handle = serial_tx_queue_handle;
    /* local_tail = serial_tx_queue_handle->queue->tail; */
}
