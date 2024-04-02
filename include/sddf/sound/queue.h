/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <sddf/sound/sound.h>
#include <sddf/util/fence.h>

#define SOUND_NUM_BUFFERS 512
#define SOUND_PCM_BUFFER_SIZE 4096

typedef enum {
    SOUND_CMD_TAKE,
    SOUND_CMD_PREPARE,
    SOUND_CMD_RELEASE,
    SOUND_CMD_START,
    SOUND_CMD_STOP,
} sound_cmd_code_t;

typedef enum {
    SOUND_S_OK = 0,
    SOUND_S_BAD_MSG,
    SOUND_S_NOT_SUPP,
    SOUND_S_IO_ERR,
    SOUND_S_BUSY,
} sound_status_t;

typedef struct sound_pcm_set_params {
    uint8_t channels;
    uint8_t format;
    uint8_t rate;
} sound_pcm_set_params_t;

typedef struct sound_cmd {
    sound_cmd_code_t code;
    uint32_t cookie;
    uint32_t stream_id;
    union {
        // Set on TAKE request
        sound_pcm_set_params_t set_params;
        // Set on all responses
        sound_status_t status;
    };
} sound_cmd_t;

typedef struct sound_pcm {
    uint32_t cookie;
    uint32_t stream_id;
    uintptr_t addr;
    unsigned int len;
    // Only used in responses.
    sound_status_t status;
    uint32_t latency_bytes;
} sound_pcm_t;

// Eventually this could be moved into its own library
typedef struct sound_queue_state {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size;
} sound_queue_state_t;

typedef struct sound_cmd_queue_t {
    sound_queue_state_t state;
    sound_cmd_t buffers[SOUND_NUM_BUFFERS];
} sound_cmd_queue_t;

typedef struct sound_pcm_queue {
    sound_queue_state_t state;
    sound_pcm_t buffers[SOUND_NUM_BUFFERS];
} sound_pcm_queue_t;

typedef struct sound_queues {
    sound_cmd_queue_t *cmd_req;
    sound_cmd_queue_t *cmd_res;

    sound_pcm_queue_t *pcm_req;
    sound_pcm_queue_t *pcm_res;
} sound_queues_t;

typedef struct sound_state {
    sound_shared_state_t *shared_state;
    sound_queues_t queues;
} sound_state_t;

/**
 * Initialise a queue. Only one side needs to call this function.
 *
 * @param queue_state 
 * @param buffer_count number of buffers in the queue
 */
static inline void sound_queue_init(sound_queue_state_t *queue_state, uint32_t buffer_count)
{
    queue_state->read_idx = 0;
    queue_state->write_idx = 0;
    queue_state->size = buffer_count;
}

/**
 * Initialises all queues to maximum capacity
 */
static inline void sound_queues_init_default(sound_queues_t *queues)
{
    sound_queue_init(&queues->cmd_req->state, SOUND_NUM_BUFFERS);
    sound_queue_init(&queues->cmd_res->state, SOUND_NUM_BUFFERS);
    sound_queue_init(&queues->pcm_req->state, SOUND_NUM_BUFFERS);
    sound_queue_init(&queues->pcm_res->state, SOUND_NUM_BUFFERS);
}

/** Returns true if CMD queue is empty */
static inline bool sound_cmd_queue_empty(sound_cmd_queue_t *q)
{
    return q->state.write_idx == q->state.read_idx;
}

/** Returns true if PCM queue is empty */
static inline bool sound_pcm_queue_empty(sound_pcm_queue_t *q)
{
    return q->state.write_idx == q->state.read_idx;
}

/**
 * Check if the command queue is full. Leave a gap of one buffer before we
 * consider the queue full.
 *
 * @param q The command queue.
 *
 * @return true indicates the command queue buffer is full, false otherwise.
 */
static inline bool sound_cmd_queue_full(sound_cmd_queue_t *q)
{
    return (q->state.write_idx - q->state.read_idx + 1) == q->state.size;
}

/**
 * Check if the PCM queue is full. Leave a gap of one buffer before we
 * consider the queue full.
 *
 * @param q The PCM queue.
 *
 * @return true indicates the command queue buffer is full, false otherwise.
 */
static inline bool sound_pcm_queue_full(sound_pcm_queue_t *q)
{
    return (q->state.write_idx - q->state.read_idx + 1) == q->state.size;
}

/**
 * Get the number of elements in a command queue.
 *
 * @param q Command queue.
 *
 * @return number of elements in the queue buffer.
 */
static inline int sound_cmd_queue_size(sound_cmd_queue_t *q)
{
    return q->state.write_idx - q->state.read_idx;
}

/**
 * Get the number of elements in a PCM queue.
 *
 * @param q PCM queue.
 *
 * @return number of elements in the queue buffer.
 */
static inline int sound_pcm_queue_size(sound_pcm_queue_t *q)
{
    return q->state.write_idx - q->state.read_idx;
}

/**
 * Enqueue a command into the command queue.
 *
 * @param queue Command queue to enqueue to
 * @param command Reference to command to enqueue
 *
 * @return -1 when command queue is full, 0 on success.
 */
static inline int sound_enqueue_cmd(sound_cmd_queue_t *queue, const sound_cmd_t *command)
{
    if (sound_cmd_queue_full(queue)) {
        return -1;
    }

    sound_cmd_t *dest = &queue->buffers[queue->state.write_idx % queue->state.size];

    dest->code = command->code;
    dest->cookie = command->cookie;
    dest->stream_id = command->stream_id;
    dest->set_params = command->set_params;

    THREAD_MEMORY_RELEASE();
    queue->state.write_idx++;

    return 0;
}

/**
 * Enqueue a PCM data element into the PCM data queue.
 *
 * @param queue PCM data queue to enqueue to.
 * @param pcm PCM data to enqueue.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int sound_enqueue_pcm(sound_pcm_queue_t *queue, sound_pcm_t *pcm)
{
    if (sound_pcm_queue_full(queue)) {
        return -1;
    }

    sound_pcm_t *data = &queue->buffers[queue->state.write_idx % queue->state.size];

    data->cookie = pcm->cookie;
    data->stream_id = pcm->stream_id;
    data->addr = pcm->addr;
    data->len = pcm->len;
    data->status = pcm->status;
    data->latency_bytes = pcm->latency_bytes;

    THREAD_MEMORY_RELEASE();
    queue->state.write_idx++;

    return 0;
}

/**
 * Dequeue an element from a command queue.
 *
 * @param queue The command queue to dequeue from.
 * @param out Pointer to write command to.
 *
 * @return -1 when command queue is empty, 0 on success.
 */
static inline int sound_dequeue_cmd(sound_cmd_queue_t *queue, sound_cmd_t *out)
{
    if (sound_cmd_queue_empty(queue)) {
        return -1;
    }

    sound_cmd_t *src = &queue->buffers[queue->state.read_idx % queue->state.size];
    out->code = src->code;
    out->cookie = src->cookie;
    out->stream_id = src->stream_id;
    out->set_params = src->set_params;

    THREAD_MEMORY_RELEASE();
    queue->state.read_idx++;

    return 0;
}

/**
 * Dequeue an element from a pcm data queue.
 *
 * @param queue The pcm data queue to dequeue from.
 * @param out Pointer to write pcm data to.
 *
 * @return -1 when command queue is empty, 0 on success.
 */
static inline int sound_dequeue_pcm(sound_pcm_queue_t *queue, sound_pcm_t *out)
{
    if (sound_pcm_queue_empty(queue)) {
        return -1;
    }

    sound_pcm_t *pcm = &queue->buffers[queue->state.read_idx % queue->state.size];

    out->cookie = pcm->cookie;
    out->stream_id = pcm->stream_id;
    out->addr = pcm->addr;
    out->len = pcm->len;
    out->status = pcm->status;
    out->latency_bytes = pcm->latency_bytes;

    THREAD_MEMORY_RELEASE();
    queue->state.read_idx++;

    return 0;
}

static inline const char *sound_command_code_str(sound_cmd_code_t code)
{
    switch (code) {
        case SOUND_CMD_TAKE:
            return "PCM_SET_PARAMS";
        case SOUND_CMD_PREPARE:
            return "PCM_PREPARE";
        case SOUND_CMD_RELEASE:
            return "PCM_RELEASE";
        case SOUND_CMD_START:
            return "PCM_START";
        case SOUND_CMD_STOP:
            return "PCM_STOP";
        default:
            return "<unknown>";
    }
}

static inline const char *sound_status_code_str(sound_status_t code)
{
    switch (code) {
        case SOUND_S_OK:
            return "OK";
        case SOUND_S_BAD_MSG:
            return "BAD_MSG";
        case SOUND_S_NOT_SUPP:
            return "NOT_SUPP";
        case SOUND_S_IO_ERR:
            return "IO_ERR";
        default:
            return "<unknown>";
    }
}

static inline const char *sound_pcm_fmt_str(sound_pcm_fmt_t fmt)
{
    switch (fmt) {
        case SOUND_PCM_FMT_IMA_ADPCM: return "IMA_ADPCM";
        case SOUND_PCM_FMT_MU_LAW:    return "MU_LAW";
        case SOUND_PCM_FMT_A_LAW:     return "A_LAW";
        case SOUND_PCM_FMT_S8:        return "S8";
        case SOUND_PCM_FMT_U8:        return "U8";
        case SOUND_PCM_FMT_S16:       return "S16";
        case SOUND_PCM_FMT_U16:       return "U16";
        case SOUND_PCM_FMT_S18_3:     return "S18_3";
        case SOUND_PCM_FMT_U18_3:     return "U18_3";
        case SOUND_PCM_FMT_S20_3:     return "S20_3";
        case SOUND_PCM_FMT_U20_3:     return "U20_3";
        case SOUND_PCM_FMT_S24_3:     return "S24_3";
        case SOUND_PCM_FMT_U24_3:     return "U24_3";
        case SOUND_PCM_FMT_S20:       return "S20";
        case SOUND_PCM_FMT_U20:       return "U20";
        case SOUND_PCM_FMT_S24:       return "S24";
        case SOUND_PCM_FMT_U24:       return "U24";
        case SOUND_PCM_FMT_S32:       return "S32";
        case SOUND_PCM_FMT_U32:       return "U32";
        case SOUND_PCM_FMT_FLOAT:     return "FLOAT";
        case SOUND_PCM_FMT_FLOAT64:   return "FLOAT64";
        case SOUND_PCM_FMT_DSD_U8:    return "DSD_U8";
        case SOUND_PCM_FMT_DSD_U16:   return "DSD_U16";
        case SOUND_PCM_FMT_DSD_U32:   return "DSD_U32";
        case SOUND_PCM_FMT_IEC958_SUBFRAME: return "IEC958_SUBFRAME";
        default:
            return "<unknown>";
    }
}
