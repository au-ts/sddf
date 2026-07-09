/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <string.h>
#include <sddf/util/cspace.h>
#include <sddf/util/printf.h>

#define HEX_TO_CHAR(hex) ((hex) < 10) ? ((hex) + '0') : ((hex) - 10 + 'A')
#define ACPI_TABLES_ALIGNMENT 0x1000

// A system could have up to 65536 PCI Segment Groups in theory, but 16 is
// sufficient in our use cases.
#define MAX_NUM_PCI_SEG_GROUP 16
#define MAX_BYTES_DSDT 10000

/* Root System Descriptor Pointer */
typedef struct acpi_rsdp {
    char         signature[8];
    uint8_t      checksum;
    char         oem_id[6];
    uint8_t      revision;
    uint32_t     rsdt_address;
    uint32_t     length;
    uint64_t     xsdt_address;
    uint8_t      extended_checksum;
    char         reserved[3];
} __attribute__((packed)) acpi_rsdp_t;

/* Generic System Descriptor Table Header */
typedef struct acpi_header {
    char         signature[4];
    uint32_t     length;
    uint8_t      revision;
    uint8_t      checksum;
    char         oem_id[6];
    char         oem_table_id[8];
    uint32_t     oem_revision;
    char         creater_id[4];
    uint32_t     creater_revision;
} __attribute__((packed)) acpi_header_t;

/* Root System Descriptor Table */
typedef struct acpi_rsdt {
    acpi_header_t  header;
    uint32_t entry[1];
} __attribute__((packed)) acpi_rsdt_t;

typedef struct acpi_fadt {
    acpi_header_t header;
    uint32_t fw_ctrl;
    uint32_t dsdt;
} __attribute__((packed)) acpi_fadt_t;

typedef struct pci_seg_group {
    uint64_t base_addr;
    uint16_t group_id;
    uint8_t bus_start;
    uint8_t bus_end;
    uint8_t reserved[4];
} __attribute__((packed)) pci_seg_group_t;

typedef struct acpi_mcfg {
    acpi_header_t header;
    uint8_t reserved[8];
    pci_seg_group_t pci_seg_group[MAX_NUM_PCI_SEG_GROUP];
} __attribute__((packed)) acpi_mcfg_t;

typedef struct acpi_dsdt {
    acpi_header_t header;
    uint8_t content[MAX_BYTES_DSDT];
} __attribute__((packed)) acpi_dsdt_t;

typedef struct bootinfo_rsdp {
    seL4_BootInfoHeader header;
    acpi_rsdp_t content;
} __attribute__((packed)) bootinfo_rsdp_t;

enum aml_encoding_value {
    ZERO_OP = 0x00,
    ONE_OP = 0x01,
    NULL_OP = 0x02,
    ALIAS_OP = 0x06,
    NAME_OP = 0x08,
    BYTE_PREFIX = 0x0A,
    WORD_PREFIX = 0x0B,
    DWORD_PREFIX = 0x0C,
    STRING_PREFIX = 0x0D,
    QWORD_PREFIX = 0x0E,
    SCOPE_OP = 0x10,
    BUFFER_PREFIX = 0x11,
    PACKAGE_PREFIX = 0x12,
    METHOD_OP = 0x14,
    EXT_OP_PREFIX = 0x5B,
    MUTEX_OP = 0x5B01,
    EVENT_OP = 0x5B02,
    OP_REGION_OP = 0x5B80,
    FIELD_OP = 0x5B81,
    DEVICE_OP = 0x5B82,
    PROCESSOR_OP = 0x5B83,
    POWER_RESOURCE_OP = 0x5B84,
    INDEX_FIELD_OP = 0x5B86,
    // Something more
    LOCAL0_OP = 0x60,
    LOCAL1_OP = 0x61,
    LOCAL2_OP = 0x62,
    LOCAL3_OP = 0x63,
    LOCAL4_OP = 0x64,
    LOCAL5_OP = 0x65,
    LOCAL6_OP = 0x66,
    LOCAL7_OP = 0x67,
    ARG0_OP = 0x68,
    ARG1_OP = 0x69,
    ARG2_OP = 0x6A,
    ARG3_OP = 0x6B,
    ARG4_OP = 0x6C,
    ARG5_OP = 0x6D,
    ARG6_OP = 0x6E,
    STORE_OP = 0x70,
    ADD_OP = 0x72,
    SUBTRACT_OP = 0x74,
    SHIFT_LEFT_OP = 0x79,
    SHIFT_RIGHT_OP = 0x7A,
    CREATE_BIT_FIELD_OP = 0x8D,
    CREATE_BYTE_FIELD_OP = 0x8C,
    CREATE_WORD_FIELD_OP = 0x8B,
    CREATE_DWORD_FIELD_OP = 0x8A,
    CREATE_QWORD_FIELD_OP = 0x8F,
    LEQUAL_OP = 0x93,
    IF_OP = 0xA0,
    ELSE_OP = 0xA1,
    RETURN_OP = 0xA4,
    // Custom Ops
    PRT_PACKAGE = 0xFE01,
};

typedef enum aml_data_type {
    DATA_OBJ_ZERO = 0x00,
    DATA_OBJ_ONE = 0x01,
    DATA_OBJ_BYTE = 0x0A,
    DATA_OBJ_WORD = 0x0B,
    DATA_OBJ_DWORD = 0x0C,
    DATA_OBJ_STRING = 0x0D,
    DATA_OBJ_QWORD = 0x0E,
    DATA_OBJ_BUFFER = 0x11,
    DATA_OBJ_PACKAGE = 0x12,
    DATA_OBJ_NODE = 0xFE,    // custom type: node
    DATA_OBJ_RET = 0xFF,     // custom type: ret_data
} aml_data_type_t;

enum aml_data_resource_type {
    EXTENDED_IRQ_DESCRIPTOR = 0x89,
    IO_PORT_DESCRIPTOR = 0x47,
    END_TAG = 0x79,
    DWORD_AS_DESCRIPTOR = 0x87,
    WORD_AS_DESCRIPTOR = 0x88,
    QWORD_AS_DESCRIPTOR = 0x8A,
};

#define MAX_NUM_AS_RESOURCES 10
#define MAX_NUM_PRT_ENTRIES 256

enum device_resource_type {
    IO_PORT = 0,
    DWORD_MEMORY,
    DWORD_IO,
    DWORD_BUS,
    WORD_MEMORY,
    WORD_IO,
    WORD_BUS,
    QWORD_MEMORY,
    QWORD_IO,
    QWORD_BUS,
};

typedef struct {
    enum device_resource_type type;
    uintptr_t min_addr;
    uintptr_t max_addr;
} device_resource_t;

typedef struct {
    uint32_t address;
    uint8_t pin;
    uint8_t gsi;
} pci_prt_t;

typedef struct {
    /* char path_name[AML_MAX_PATH_STR]; */
    /* uint32_t path_len; */
    uint32_t bus_start;
    uint32_t bus_end;
    device_resource_t dev_resources[MAX_NUM_AS_RESOURCES];
    uint8_t num_dev_resources;
    pci_prt_t prt_entries[MAX_NUM_PRT_ENTRIES];
    uint8_t num_prt_entries;
} pci_bridge_t;

typedef struct {
    pci_seg_group_t pci_seg_groups[MAX_NUM_PCI_SEG_GROUP];
    uint32_t num_pci_groups;
    pci_bridge_t bridges[10];
    uint32_t num_bridges;
    cnode_specs_t cnode_specs;
} pci_resources_t;

typedef struct {
    uint8_t  tag;            // 0x89
    uint16_t length;         // Length of data (usually 13 bytes)
    uint8_t  vector_flags;   //
    uint8_t  table_len;      //
    uint8_t  irq_num;        //
    // Optional 'Resource Source' string could follow here
} __attribute__((packed)) acpi_ext_irq_t;

typedef struct {
    uint8_t  tag;            // 0x88
    uint16_t length;         // Length of data (usually 13 bytes)
    uint8_t  resource_type;  // 0=Memory, 1=IO, 2=BusNumber
    uint8_t  flags;          // General flags (Dec, Min, Max, etc.)
    uint8_t  type_flags;     // Type-specific flags
    uint16_t granularity;    // Address granularity
    uint16_t min_address;    // Range minimum
    uint16_t max_address;    // Range maximum
    uint16_t translation;    // Address translation offset
    uint16_t address_length; // Length of the address range
    // Optional 'Resource Source' string could follow here
} __attribute__((packed)) acpi_word_address_space_t;

typedef struct {
    uint8_t  tag;            // 0x87
    uint16_t length;         // 0x0017 (23 bytes)
    uint8_t  resource_type;  // 0=Memory, 1=IO, 2=BusNumber
    uint8_t  flags;          // General Flags (Producer, Decode, etc.)
    uint8_t  type_flags;     // Type-specific flags (e.g., Cacheable)
    uint32_t granularity;    // Address Granularity
    uint32_t min_address;    // Address Minimum
    uint32_t max_address;    // Address Maximum
    uint32_t translation;    // Address Translation Offset
    uint32_t address_length; // Address Length
    // Optional: Resource Source Index and String could follow
} __attribute__((packed)) acpi_dword_address_space_t;

typedef struct {
    uint8_t  tag;            // 0x8A
    uint16_t length;         // 0x002B (43 bytes)
    uint8_t  resource_type;  // 0=Memory, 1=IO, 2=BusNumber
    uint8_t  flags;          // General Flags (Producer, Decode, etc.)
    uint8_t  type_flags;     // Type-specific flags
    uint64_t granularity;    // Address Granularity
    uint64_t min_address;    // Address Minimum
    uint64_t max_address;    // Address Maximum
    uint64_t translation;    // Address Translation Offset
    uint64_t address_length; // Address Length
    // Optional: Resource Source Index and String follow if length > 43
} __attribute__((packed)) acpi_qword_address_space_t;

typedef struct {
    uint8_t  tag;            // 0x47 (Type 0x08, Length 7)
    uint8_t  info;           // Flags (16-bit decode, etc.)
    uint16_t min_address;    // Minimum I/O address
    uint16_t max_address;    // Maximum I/O address
    uint8_t  alignment;      // Alignment requirement
    uint8_t  address_length; // Number of ports used
} __attribute__((packed)) acpi_io_port_t;

typedef struct acpi_crs_list {
    enum aml_data_resource_type resource_type;
    uintptr_t data_addr;
    struct acpi_crs_list *next;
} __attribute__((packed)) acpi_crs_list_t;

typedef struct {
    uint8_t* start;
    uint8_t* current;
} scanner_t;

extern scanner_t scanner;
extern pci_resources_t *pci_resources;

// ====== Refactor =====
typedef struct {
    void *start;
    void *next;
    void *end;
} mempool_t;

typedef struct {
    uint64_t value;
    aml_data_type_t type;
    uint32_t length;
} aml_data_t;

typedef struct aml_namespace_node {
    uint8_t *pkt_start;
    uint8_t *pkt_end;
    struct aml_namespace_node *parent;  // parent
    struct aml_namespace_node *child;   // first child object
    struct aml_namespace_node *next;    // siblings
    char name[5];                       // Name Segment
    enum aml_encoding_value op_code;
    aml_data_t data;                    // Store evaluation results
    bool evaluated;                     // If this has been evaluated
} aml_namespace_node_t;

typedef struct parse_state {
    struct parse_state *parent;
    uint8_t *node_start;
    uint8_t *pkt_end;
    aml_namespace_node_t *node;
    uint16_t op_code;
    uint8_t stage_idx;
    uint8_t num_args;
    aml_data_t arguments[10];
    bool evaluation;
    bool if_condition;
} parse_state_t;

#define MAX_NUM_ACPI_TABLES 20

typedef enum {
    ACPI_TABLE_TYPE_FADT,
    ACPI_TABLE_TYPE_DSDT,
    ACPI_TABLE_TYPE_SSDT,
    ACPI_TABLE_TYPE_MCFG,
} acpi_table_type_t;

typedef struct {
    acpi_header_t *tables[MAX_NUM_ACPI_TABLES];
    uintptr_t tables_end;
    uintptr_t mem_end;
    uint32_t alignment;
    uint32_t num_tables;
} acpi_tables_summary_t;

extern mempool_t aml_namespace_mempool;
extern aml_namespace_node_t namespace_root;

void scan_namespace_tree(aml_namespace_node_t *namespace, uint8_t *namespace_end);
aml_namespace_node_t *find_child_node_by_name(aml_namespace_node_t *node, const char *name_segment);
uint8_t find_decendant_nodes_by_name(aml_namespace_node_t *node, const char *name_segment, aml_namespace_node_t **lookup_results, uint8_t num_results);
void read_eisa_id(aml_namespace_node_t *node, char *eisa_id_str);
aml_data_t eval_namespace_node(aml_namespace_node_t *node, uint8_t num_args, aml_data_t argv[]);
uint8_t advance();
void set_scanner_to(uint8_t *start);
uint8_t *get_pkt_end();
void eval_data_object(pci_prt_t *prt, uint8_t *pkt_end);
void parse_prt_package(aml_data_t prt_data, uint32_t bridge_idx);
