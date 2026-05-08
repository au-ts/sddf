/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <sddf/util/printf.h>

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("SND DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_dprintf("SND DRIVER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

struct virtio_snd_config {
    uint32_t jacks;
    uint32_t streams;
    uint32_t chmaps;
};

enum {
    /* jack control request types */
    VIRTIO_SND_R_JACK_INFO = 1,
    VIRTIO_SND_R_JACK_REMAP,
    /* PCM control request types */
    VIRTIO_SND_R_PCM_INFO = 0x0100,
    VIRTIO_SND_R_PCM_SET_PARAMS,
    VIRTIO_SND_R_PCM_PREPARE,
    VIRTIO_SND_R_PCM_RELEASE,
    VIRTIO_SND_R_PCM_START,
    VIRTIO_SND_R_PCM_STOP,
    /* channel map control request types */
    VIRTIO_SND_R_CHMAP_INFO = 0x0200,
    /* jack event types */
    VIRTIO_SND_EVT_JACK_CONNECTED = 0x1000,
    VIRTIO_SND_EVT_JACK_DISCONNECTED,
    /* PCM event types */
    VIRTIO_SND_EVT_PCM_PERIOD_ELAPSED = 0x1100,
    VIRTIO_SND_EVT_PCM_XRUN,
    /* common status codes */
    VIRTIO_SND_S_OK = 0x8000,
    VIRTIO_SND_S_BAD_MSG,
    VIRTIO_SND_S_NOT_SUPP,
    VIRTIO_SND_S_IO_ERR
};

/* a common header */
struct virtio_snd_hdr {
    uint32_t code;
};

/* an event notification */
struct virtio_snd_event {
    struct virtio_snd_hdr hdr;
    uint32_t data;
};

struct virtio_snd_query_info {
    struct virtio_snd_hdr hdr;
    uint32_t start_id;
    uint32_t count;
    uint32_t size;
};

struct virtio_snd_info {
    uint32_t hda_fn_nid;
};

/* supported PCM stream features */
enum {
    VIRTIO_SND_PCM_F_SHMEM_HOST = 0,
    VIRTIO_SND_PCM_F_SHMEM_GUEST,
    VIRTIO_SND_PCM_F_MSG_POLLING,
    VIRTIO_SND_PCM_F_EVT_SHMEM_PERIODS,
    VIRTIO_SND_PCM_F_EVT_XRUNS
};

/* supported PCM sample formats */
enum {
    /* analog formats (width / physical width) */
    VIRTIO_SND_PCM_FMT_IMA_ADPCM = 0, /* 4 / 4 bits */
    VIRTIO_SND_PCM_FMT_MU_LAW, /* 8 / 8 bits */
    VIRTIO_SND_PCM_FMT_A_LAW, /* 8 / 8 bits */
    VIRTIO_SND_PCM_FMT_S8, /* 8 / 8 bits */
    VIRTIO_SND_PCM_FMT_U8, /* 8 / 8 bits */
    VIRTIO_SND_PCM_FMT_S16, /* 16 / 16 bits */
    VIRTIO_SND_PCM_FMT_U16, /* 16 / 16 bits */
    VIRTIO_SND_PCM_FMT_S18_3, /* 18 / 24 bits */
    VIRTIO_SND_PCM_FMT_U18_3, /* 18 / 24 bits */
    VIRTIO_SND_PCM_FMT_S20_3, /* 20 / 24 bits */
    VIRTIO_SND_PCM_FMT_U20_3, /* 20 / 24 bits */
    VIRTIO_SND_PCM_FMT_S24_3, /* 24 / 24 bits */
    VIRTIO_SND_PCM_FMT_U24_3, /* 24 / 24 bits */
    VIRTIO_SND_PCM_FMT_S20, /* 20 / 32 bits */
    VIRTIO_SND_PCM_FMT_U20, /* 20 / 32 bits */
    VIRTIO_SND_PCM_FMT_S24, /* 24 / 32 bits */
    VIRTIO_SND_PCM_FMT_U24, /* 24 / 32 bits */
    VIRTIO_SND_PCM_FMT_S32, /* 32 / 32 bits */
    VIRTIO_SND_PCM_FMT_U32, /* 32 / 32 bits */
    VIRTIO_SND_PCM_FMT_FLOAT, /* 32 / 32 bits */
    VIRTIO_SND_PCM_FMT_FLOAT64, /* 64 / 64 bits */
    /* digital formats (width / physical width) */
    VIRTIO_SND_PCM_FMT_DSD_U8, /* 8 / 8 bits */
    VIRTIO_SND_PCM_FMT_DSD_U16, /* 16 / 16 bits */
    VIRTIO_SND_PCM_FMT_DSD_U32, /* 32 / 32 bits */
    VIRTIO_SND_PCM_FMT_IEC958_SUBFRAME /* 32 / 32 bits */
};

/* supported PCM frame rates */
enum {
    VIRTIO_SND_PCM_RATE_5512 = 0,
    VIRTIO_SND_PCM_RATE_8000,
    VIRTIO_SND_PCM_RATE_11025,
    VIRTIO_SND_PCM_RATE_16000,
    VIRTIO_SND_PCM_RATE_22050,
    VIRTIO_SND_PCM_RATE_32000,
    VIRTIO_SND_PCM_RATE_44100,
    VIRTIO_SND_PCM_RATE_48000,
    VIRTIO_SND_PCM_RATE_64000,
    VIRTIO_SND_PCM_RATE_88200,
    VIRTIO_SND_PCM_RATE_96000,
    VIRTIO_SND_PCM_RATE_176400,
    VIRTIO_SND_PCM_RATE_192000,
    VIRTIO_SND_PCM_RATE_384000
};

struct virtio_snd_pcm_info {
    struct virtio_snd_info hdr;
    uint32_t features; /* 1 << VIRTIO_SND_PCM_F_XXX */
    uint64_t formats; /* 1 << VIRTIO_SND_PCM_FMT_XXX */
    uint64_t rates; /* 1 << VIRTIO_SND_PCM_RATE_XXX */
    uint8_t direction;
    uint8_t channels_min;
    uint8_t channels_max;
    uint8_t padding[5];
};

static void virtio_snd_print_config(volatile struct virtio_snd_config *config)
{
    LOG_DRIVER("jacks: 0x%x\n", config->jacks);
    LOG_DRIVER("streams: 0x%x\n", config->streams);
    LOG_DRIVER("chmaps: 0x%x\n", config->chmaps);
}
