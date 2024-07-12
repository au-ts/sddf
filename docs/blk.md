# sDDF Block

This document describes how to set up and interface with the sDDF block subsystem

## System architecture
The block subsystem consists of a set of components that communicate via shared data structures
and signalling through microkit channels. The components are **clients**, who can send
requests via a queue to a **block virtualiser**, which multiplexes the requests from multiple
clients to be handled by the **block driver**. The communication between each component happens
over 4 shared memory regions: the request and response queue metadata regions, the data region,
and the configuration region.

## Client protection domain
Clients of the block subsystem has to include the block queue library and a blk config file.
The block queues have to be initialised before operating on it. Clients should read from the
blk_config file to access memory mapping information, including the request and response queue
sizes needed to initialise the queues.

The notified handler from the client will execute when the virtualiser signals the client to indicate that there are new entries in the response queue. You must put handling logic there to handle the responses.

An [example](https://github.com/au-ts/libvmm/blob/main/examples/virtio/client_vmm.c) of a client can be found in libvmm's virtio example

## System description format
The system description file must contain
a block driver protection domain, a block virtualiser protection
domain, and client protection domains of the block subsystem.
Between each client and virtualiser, there must be one of each 4 types of memory regions
in the sDDF block protocol to be mapped into both protection domains.
The same applies between the virtualiser
and the driver with the exception of the data region, which is not required
as block devices use DMA.
A channel must then be created for each communicating protection domain.
To allow the virtualiser to translate client offsets to I/O addresses,
the virtualiser must be provided with the physical address of the clients' data region.

The libvmm virtio example has a [prototype](https://github.com/au-ts/libvmm/blob/main/examples/virtio/board/qemu_arm_virt/virtio.system).

### Mapped regions
The block virtualiser and driver components implemented in this repository requires the mapping
to be done a certain way:

* The metadata regions and shared configuration page must be mapped in with caching
set to false. Caching for metadata regions needs to be set false in order to prevent cache
incoherence when using linux driver VMs, which maps these regions as false
using its UIO mechanism. The virtualiser only handles the cache management of the data
region so only caching for that region can be true.

#### Virtualiser:
* Access to the physical address of client data regions.
* The clients mappings must be layed out contiguously for each memory region type. This is
done to allow generic handling of any number of clients.
* Required memory region mappings and their hardcoded setvaddr:
  * Driver config region = **blk_config_driver**
  * Driver request region = **blk_req_queue_driver**
  * Driver response region = **blk_resp_queue_driver**
  * Clients base config region = **blk_config**
  * Clients base request region = **blk_req_queue**
  * Clients base response region = **blk_resp_queue**
  * Clients base data region = **blk_client_data_start**

#### Driver
* Required memory region mappings and their hardcoded setvaddr:
  * Config region = **blk_config**
  * Request region = **blk_req_queue**
  * Response region = **blk_resp_queue**

#### Client
* Required memory region mappings:
  * Config region,
  * Request region,
  * Response region,
  * Data region,
* Client decides what symbols and setvaddr they want to match.


### Channel numbers
There are specific channel IDs components are hardcoded to communicate to each other with.
* Driver - Virtualiser:
The driver must have channel id 0. The virtualiser must have channel id 0.
* Virtualiser - Client:
The virtualiser must have channel id ranging from 1-n, where n is number of clients. The client
ids must be chronological and start from 1. For example. if there are 3 clients the virtualiser
must use id 1, 2 and 3 for its 3 channels with the clients.

## Blk config file
A blk_config.h header file must be provided when building the system that propagates memory
region information from the system description file into the C code.

The blk_config file must contain:
* number of clients:
    ```
    #define BLK_NUM_CLIENTS
    ```
* implementation for these functions:
    ```
    static inline blk_storage_info_t *blk_virt_cli_config_info(blk_storage_info_t *info, unsigned int id)
    static inline uintptr_t blk_virt_cli_data_region(uintptr_t data, unsigned int id)
    static inline uint64_t blk_virt_cli_data_region_size(unsigned int id)
    static inline blk_req_queue_t *blk_virt_cli_req_queue(blk_req_queue_t *req, unsigned int id)
    static inline blk_resp_queue_t *blk_virt_cli_resp_queue(blk_resp_queue_t *resp, unsigned int id)
    static inline uint32_t blk_virt_cli_queue_size(unsigned int id)
    static inline uint32_t blk_cli_queue_size(char *pd_name)
    ```
    The id argument specifies the client id.
* size of the block queue between the virtualiser and driver
    ```
    #define BLK_QUEUE_SIZE_DRIV
    ```

For the virtualiser, the SDF only exposes a pointer to the base address of each memory
region type. Thus each client's memory region is accessed via an offset into this base address.
The offset is the size of the region.

A recommended prototype for a blk_config file with two clients has the following:
```
#define BLK_NUM_CLIENTS 2

#define BLK_NAME_CLI0                      "CLIENT_VMM-1"
#define BLK_NAME_CLI1                      "CLIENT_VMM-2"

#define BLK_QUEUE_SIZE_CLI0                 1024
#define BLK_QUEUE_SIZE_CLI1                 1024
#define BLK_QUEUE_SIZE_DRIV                 (BLK_QUEUE_SIZE_CLI0 + BLK_QUEUE_SIZE_CLI1)

#define BLK_REGION_SIZE                     0x200000
#define BLK_CONFIG_REGION_SIZE_CLI0         BLK_REGION_SIZE
#define BLK_CONFIG_REGION_SIZE_CLI1         BLK_REGION_SIZE

#define BLK_DATA_REGION_SIZE_CLI0           BLK_REGION_SIZE
#define BLK_DATA_REGION_SIZE_CLI1           BLK_REGION_SIZE

#define BLK_QUEUE_REGION_SIZE_CLI0          BLK_REGION_SIZE
#define BLK_QUEUE_REGION_SIZE_CLI1          BLK_REGION_SIZE
#define BLK_QUEUE_REGION_SIZE_DRIV          BLK_REGION_SIZE
```

This allows you to specify which client id maps to which protection domain
in the system description file, and work out the memory region offsets
to implement functions like the following:
```
static inline uintptr_t blk_virt_cli_data_region(uintptr_t data, unsigned int id)
{
    switch (id) {
    case 0:
        return data;
    case 1:
        return (uintptr_t)data + BLK_DATA_REGION_SIZE_CLI0;
    default:
        return 0;
    }
}
```

There is no check to ensure that any QUEUE_SIZE you define will not cause the queues to
overflow the size of its associated memory region you've declared in the system
description file. The user has to check themselves whether the declared sizes are OK.


## Makefile
There are no Makefile snippets for the block subsystem as of yet, unlike the serial and
network subsystems.

Your linker must include sDDF's include directory, and the directory
containing the blk_config.h header file.

You must compile the block virtualiser and driver yourself,
and include their object files to the microkit image list.

Note that the block virtualiser needs to link with `libsddf_util_debug.a`.
Below is a provided snippet on how to build it in your Makefile
```
$(BUILD_DIR)/util/%.o: ${SDDF_DIR}/util/%.c
	${CC} ${CFLAGS} -c -o $@ $<

SDDF_LIB_UTIL_DBG_OBJS := cache.o sddf_printf.o newlibc.o assert.o putchar_debug.o bitarray.o fsmalloc.o

$(BUILD_DIR)/libsddf_util_debug.a: $(addprefix ${BUILD_DIR}/util/, ${SDDF_LIB_UTIL_DBG_OBJS})
	${AR} rv $@ $^
	${RANLIB} $@
```

## Configuration
* The data region sizes and metadata region sizes can be tuned to suit your
needs. Users specify these via the blk_config file, and ensuring that there is enough space allocated in the system description file.

* The number of clients specified in blk_config file has to match the number
of client connections to the virtualiser.
