/* The policy of the virt tx is that all clients can always request to transmit */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/util.h>
#include <serial_config.h>
#include "uart.h"

#define DRIVER_CH 0
#define CLIENT_OFFSET 1

#define COLOUR_START_LEN 5
#define COLOUR_END_LEN 4

#define MAX_NUM_CLIENTS 8

/* This is a simple sanity check that we have defined as many colours
   as the user as specified clients */
#if NUM_CLIENTS > MAX_NUM_CLIENTS && defined(SERIAL_TRANSFER_WITH_COLOUR)
#error "There are more clients then there are colours to differentiate them"
#endif

char *client_colours[MAX_NUM_CLIENTS] = { "\x1b[30m", "\x1b[31m", "\x1b[32m", "\x1b[33m", "\x1b[34m", "\x1b[35m", "\x1b[36m", "\x1b[37m" };
char *client_colour_end = "\x1b[0m";

/* Memory regions as defined in the system file. All data regions must be mapped into the same virtual address in each client! */

// Transmit queues with the driver
uintptr_t tx_free_driver;
uintptr_t tx_active_driver;
uintptr_t tx_data_driver;

// Transmit queues with the client. Client free, active and data regions must be mapped in contiguously
uintptr_t tx_free_client0;
uintptr_t tx_active_client0;

serial_queue_handle_t drv_tx_queue;
serial_queue_handle_t tx_queue[NUM_CLIENTS];

size_t copy_with_colour(size_t client, size_t buffer_len, char *driver_buf, char *client_buf)
{
    size_t len_copied = 0;
    // assert(buffer_len + COLOUR_START_LEN + COLOUR_START_LEN <= BUFFER_SIZE);
    /* First copy the colour start bytes */
    memcpy((char *) driver_buf, client_colours[client], COLOUR_START_LEN);
    len_copied += COLOUR_START_LEN;
    /* Copy the actual TX data */
    char *dest_buffer = driver_buf + COLOUR_START_LEN;
    memcpy(dest_buffer, client_buf, buffer_len);
    len_copied += buffer_len;
    /* And then finally the colour end bytes */
    memcpy((char *)(dest_buffer + buffer_len), client_colour_end, COLOUR_END_LEN);
    len_copied += COLOUR_END_LEN;

    return len_copied;
}

size_t copy_normal(size_t buffer_len, char *driver_buf, char *client_buf)
{
    /* All we need to do is copy the client buffer into the driver buffer. */
    memcpy(driver_buf, client_buf, buffer_len);

    return buffer_len;
}

int handle_tx(int curr_client)
{
    // Copy data from the client queues to the driver queue.
    uintptr_t client_buf = 0;
    unsigned int client_buf_len = 0;

    // Loop over all clients here
    for (int client = 0; client < NUM_CLIENTS; client++) {
        // The client can plug their queue. If plugged, we won't process it.
        if (serial_queue_plugged(tx_queue[client].active)) {
            continue;
        }
        while (!serial_dequeue_active(&tx_queue[client], &client_buf, &client_buf_len)) {
            // We want to enqueue into the drivers active queue
            uintptr_t driver_buf = 0;
            unsigned int driver_buf_len = 0;

            int ret = serial_dequeue_free(&drv_tx_queue, &driver_buf, &driver_buf_len);
            if (ret != 0) {
                microkit_dbg_puts("Failed to dequeue buffer from drv tx avail queue\n");
                return 1;
            }

            /*
             * Depending on the overall system, we may want to add colour to
             * the transmit data in order to easily identify which client the
             * data belongs to when looking at the serial output. This makes
             * the most sense when you have, for example, multiple client
             * consoles being multiplexed. However, not all systems will act
             * like that even if they have multiple clients, which is why this
             * is configurable behaviour.
             */
#ifdef SERIAL_TRANSFER_WITH_COLOUR
            size_t len_copied = copy_with_colour(client, client_buf_len, (char *)driver_buf, (char *)client_buf);
#else
            size_t len_copied = copy_normal(client_buf_len, (char *)driver_buf, (char *)client_buf);
#endif

            ret = serial_enqueue_active(&drv_tx_queue, driver_buf, len_copied);
            if (ret != 0) {
                microkit_dbg_puts("Failed to enqueue buffer to drv tx active queue\n");
                // Don't know if I should return here, because we need to enqueue a
                // serpeate buffer
            }

            /*
             * Now that we've finished processing the client's active buffer, we
             * can put it back in the free queue. Note that the *whole* buffer is
             * free now, which is why the length we enqueue is the maximum
             * buffer length.
             */
            serial_enqueue_free(&tx_queue[client], client_buf, BUFFER_SIZE);
        }
    }

    microkit_notify(DRIVER_CH);
    return 0;
}

void init(void)
{
    serial_queue_init(&drv_tx_queue, (serial_queue_t *)tx_free_driver, (serial_queue_t *)tx_active_driver, TX_QUEUE_SIZE_DRIV);
    serial_buffers_init(&drv_tx_queue, tx_data_driver);
    virt_queue_init_sys(microkit_name, tx_queue, tx_free_client0, tx_active_client0);
}

void notified(microkit_channel ch)
{
    // We should only ever recieve notifications from the client
    // Sanity check the client
    if (ch == DRIVER_CH || ch > NUM_CLIENTS) {
        microkit_dbg_puts("Received a bad client channel\n");
        return;
    }

    handle_tx(ch);
}
