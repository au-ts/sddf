#pragma once

#include <stdint.h>

#define MAX_ARP_ENTRIES 512
#define ARP_BUFFER_SIZE 128

typedef struct arp_entry {
    uint8_t mac_addr[ETH_HWADDR_LEN];
    /* @kwinter: Add a timeout for stale ARP entiries*/
    // uint32_t timeout;
    bool valid;
} arp_entry_t;

/* These are the structs that will live inside the buffer list. */

typedef struct arp_request {
    uint32_t ip_addr;
    uint8_t mac_addr[ETH_HWADDR_LEN];
    /* If valid is false on reply, drop the packet. */
    bool valid;
} arp_request_t;

typedef struct arp_queue {
    /* index to insert at */
    uint16_t tail;
    /* index to remove from */
    uint16_t head;
   /* buffer descripter array */
    arp_request_t queue[MAX_ARP_ENTRIES];
} arp_queue_t;

typedef struct arp_queue_handle {
    /* arp requests */
    arp_queue_t request;
    /* responses to arp requests */
    arp_queue_t response;
    /* capacity of the queues */
    uint32_t capacity;
} arp_queue_handle_t;

/**
 * Get the number of requests/responses enqueued into a queue.
 *
 * @param queue queue handle for the queue to get the length of.
 *
 * @return number of queue enqueued into a queue.
 */
static inline uint16_t arp_queue_length(arp_queue_t *queue)
{
    return queue->tail - queue->head;
}

/**
 * Check if the request queue is empty.
 *
 * @param queue queue handle for the request queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline bool arp_queue_empty_request(arp_queue_handle_t *queue)
{
    return queue->request.tail - queue->request.head == 0;
}

/**
 * Check if the response queue is empty.
 *
 * @param queue queue handle for the response queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline bool arp_queue_empty_response(arp_queue_handle_t *queue)
{
    return queue->response.tail - queue->response.head == 0;
}

/**
 * Check if the request queue is full.
 *
 * @param queue queue handle for the request queue to check.
 *
 * @return true indicates the queue is full, false otherwise.
 */
static inline bool arp_queue_full_request(arp_queue_handle_t *queue)
{
    return queue->request.tail - queue->request.head == queue->capacity;
}

/**
 * Check if the reponse queue is full.
 *
 * @param queue queue handle for the response queue to check.
 *
 * @return true indicates the queue is full, false otherwise.
 */
static inline bool arp_queue_full_active(arp_queue_handle_t *queue)
{
    return queue->response.tail - queue->response.head == queue->capacity;
}

/**
 * Enqueue an element into a free queue.
 *
 * @param queue queue to enqueue into.
 * @param buffer request to be enqueued.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int arp_enqueue_request(arp_queue_handle_t *queue, arp_request_t request)
{
    if (arp_queue_full_free(queue)) {
        return -1;
    }

    arp_request_t req = queue->request.queue[queue->request.tail % queue->capacity];
    sddf_memcpy(&req, &request, sizeof(arp_request_t));

    queue->request.tail++;

    return 0;
}

/**
 * Enqueue an element into an response queue.
 *
 * @param queue queue to enqueue into.
 * @param buffer reponse to be enqueued.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int arp_enqueue_response(arp_queue_handle_t *queue, arp_request_t response)
{
    if (arp_queue_full_active(queue)) {
        return -1;
    }

    arp_request_t resp = queue->response.queue[queue->response.tail % queue->capacity];
    sddf_memcpy(&resp, &response, sizeof(arp_request_t));

    queue->response.tail++;

    return 0;
}

/**
 * Dequeue an element from the request queue.
 *
 * @param queue queue handle to dequeue from.
 * @param buffer pointer to request to be dequeued.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int arp_dequeue_request(arp_queue_handle_t *queue, arp_request_t *request)
{
    if (arp_queue_empty_request(queue)) {
        return -1;
    }

    arp_request_t req = queue->request.queue[queue->request.head % queue->capacity];
    sddf_memcpy(request, &req, sizeof(arp_request_t));

    queue->request.head++;

    return 0;
}

/**
 * Dequeue an element from the reponse queue.
 *
 * @param queue queue handle to dequeue from.
 * @param buffer pointer to reponse to be dequeued.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int arp_dequeue_response(arp_queue_handle_t *queue, arp_request_t *response)
{
    if (arp_queue_empty_response(queue)) {
        return -1;
    }

    arp_request_t resp = queue->response.queue[queue->response.head % queue->capacity];
    sddf_memcpy(response, &resp, sizeof(arp_request_t));

    queue->response.head++;

    return 0;
}

/**
 * Initialise the shared queue.
 *
 * @param queue queue handle to use.
 * @param free pointer to free queue in shared memory.
 * @param active pointer to active queue in shared memory.
 * @param capacity capacity of the free and active queues.
 */
static inline void arp_handle_init(arp_queue_handle_t *queue, uint32_t capacity)
{
    queue->capacity = capacity;
}

/**
 * Initialise the request queue by filling with all request queue.
 *
 * @param queue queue handle to use.
 * @param base_addr start of the memory region the offsets are applied to (only used between virt and driver)
 */
// static inline void arp_queue_init(arp_queue_handle_t *queue, uintptr_t base_addr)
// {
//     for (uint32_t i = 0; i < queue->capacity; i++) {
//         queue->request[i] = {0};
//         queue->response[i] = {0};
//     }
// }
