/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <string.h>
#include <sddf/util/printf.h>

#define HEX_TO_CHAR(hex) ((hex) < 10) ? ((hex) + '0') : ((hex) - 10 + 'A')

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
    ALIAS_OP = 0x06,
    NAME_OP = 0x08,
    BYTE_PREFIX = 0x0A,
    WORD_PREFIX = 0x0B,
    DWORD_PREFIX = 0x0C,
    STRING_PREFIX = 0x0D,
    QWORD_PREFIX = 0x0E,
    SCOPE_OP = 0x10,
    PACKAGE_OP = 0x12,
    METHOD_OP = 0x14,
    EXT_OP_PREFIX = 0x5B,
    DEVICE_OP = 0x5B82,
    // Something more
    IF_OP = 0xA0,
    ELSE_OP = 0xA1,
    RETURN_OP = 0xA4,
    NULL_OP = 0xFFFF,
};

enum aml_data_object_type {
    DATA_OBJ_ZERO = 0x00,
    DATA_OBJ_ONE = 0x01,
    DATA_OBJ_BYTE = 0x0A,
    DATA_OBJ_WORD = 0x0B,
    DATA_OBJ_DWORD = 0x0C,
    DATA_OBJ_STRING = 0x0D,
    DATA_OBJ_BUFFER = 0x11,
    DATA_OBJ_PACKAGE = 0x12,
};

enum aml_data_resource_type {
    EXTENDED_IRQ_DESCRIPTOR = 0x89,
    IO_PORT_DESCRIPTOR = 0x47,
    DWORD_AS_DESCRIPTOR = 0x87,
    WORD_AS_DESCRIPTOR = 0x88,
    QWORD_AS_DESCRIPTOR = 0x8A,
};

// Each path segment has exactly 4 characters, up to 25 segments are assumed
#define AML_MAX_PATH_STR 100
typedef struct {
    char name_str[AML_MAX_PATH_STR];
    uint32_t len;
} aml_path_seg_t;

// see Section 20.2.4 Package Length Encoding
typedef uint32_t aml_pkg_len_t;

typedef struct {
    char path_name[AML_MAX_PATH_STR];
    uint32_t path_len;
    uint32_t bus_start;
    uint32_t bus_end;
} pci_bridge_t;

typedef struct {
    pci_seg_group_t pci_seg_groups[MAX_NUM_PCI_SEG_GROUP];
    uint32_t num_pci_groups;
    pci_bridge_t bridges[10];
    uint32_t num_bridges;
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

typedef struct aml_object {
    uint8_t *start;
    struct aml_object *parent;  // parent
    struct aml_object *child;   // first child object
    struct aml_object *next;    // siblings
    char name[5];    // Name Segment
    enum aml_encoding_value op_code;
} aml_object_t;

typedef struct aml_object_pool {
    uintptr_t next;
    uintptr_t end;
} aml_object_pool_t;

typedef struct object_lookup_list {
    aml_object_t *node;
    aml_object_t *next;
} object_lookup_list_t;

void scan_objects(aml_object_t *parent, uint8_t *next_parent_start);
void print_object_tree(aml_object_t *node, uint8_t depth);
void read_eisa_id(aml_object_t *node, char *eisa_id_str);
acpi_crs_list_t *extract_pcie_crs(aml_object_t *node);
void print_crs_list(acpi_crs_list_t *crs_list);
bool extract_pcie_prt(aml_object_t *node, char *package_name);
void extract_prt_package(aml_object_t *node);
void query_all_objects_by_name(aml_object_t *node, const char *name_segment);
aml_object_t *query_child_object_by_name(aml_object_t *node, const char *name_segment);
aml_object_t *query_same_domain_object_by_name(aml_object_t *node, const char *name_segment);

extern uintptr_t aml_object_pool_start;
extern scanner_t scanner;
extern aml_object_pool_t object_pool;
extern aml_object_t object_root;
extern pci_resources_t pci_resources;
extern aml_object_t *lookup_results[50];
extern uint32_t lookup_cnt;

extern const char acpi_str_fadt[];
extern const char acpi_str_mcfg[];
extern const char acpi_str_hid[];
extern const char acpi_str_crs[];
extern const char acpi_str_prt[];
extern const char eisaid_str_pcie[];
