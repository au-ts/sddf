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
    METHOD_OP = 0x14,
    EXT_OP_PREFIX = 0x5B,
    DEVICE_OP = 0x5B82,
    // Something more
    IF_OP = 0xA0,
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

/* uint32_t get_pkt_len(uint8_t *pktlen_encoding) */
/* { */
/*     uint8_t byte_data_cnt = pktlen_encoding[0] >> 6; */

/*     // pktLength encoded in bits 5-0 if one byte long */
/*     if (byte_data_cnt == 0) { */
/*         return pktlen_encoding[0] & 0x3F; */
/*     } */

/*     uint32_t pkt_len = 0; */
/*     do { */
/*         pkt_len = (pkt_len << 8) + pktlen_encoding[byte_data_cnt]; */
/*         sddf_dprintf("byte %d: %u\n", byte_data_cnt, pktlen_encoding[byte_data_cnt]); */
/*         sddf_dprintf(" -- pkt_len: %u\n", pkt_len); */
/*     } while (--byte_data_cnt); */
/*     // pktLength encoded in bits 3-0 if multiple bytes */
/*     pkt_len = (pkt_len << 4) + (pktlen_encoding[0] & 0xF); */
/*     sddf_dprintf(" -- pkt_len: %u\n", pkt_len); */
/*     return pkt_len; */
/* } */

/* uint32_t get_pktlen_bytes(uint8_t *pktlen_encoding) */
/* { */
/*     return 1 + (pktlen_encoding[0] >> 6); */
/* } */

/* // see Section 20.2.2 Name Objects Encoding */
/* uint32_t get_name_string(uint8_t *name_encoding, char *name_str) */
/* { */
/*     if ((name_encoding[0] >= 'A' && name_encoding[0] < 'Z') || name_encoding[0] == '_') { */
/*         // Name Segment */
/*         memcpy(name_str, name_encoding, 4); */
/*         name_str[4] = '\0'; */
/*         return 4; */
/*     } else if (name_encoding[0] == '\\') { */
/*         // Root Path */
/*         name_str[0] = '\\'; */
/*         return 1 + get_name_string(&name_encoding[1], &name_str[1]); */
/*     } else if (name_encoding[0] == 0x2E) { */
/*         // Dual Name Segment */
/*         memcpy(name_str, &name_encoding[1], 8); */
/*         name_str[8] = '\0'; */
/*         return 9; */
/*     } else if (name_encoding[0] == 0x2F) { */
/*         // Multiple Name Segment */
/*         memcpy(name_str, &name_encoding[2], name_encoding[1]); */
/*         name_str[name_encoding[1]] = '\0'; */
/*         return 1 + name_encoding[1]; */
/*     } */
/*     return 0; */
/* } */

/* // get length of data included in Name Object, including bytes specifying length */
/* uint32_t get_name_data_len(uint8_t *data_encoding) */
/* { */
/*     switch (data_encoding[0]) { */
/*         case DATA_OBJ_ZERO: */
/*         case DATA_OBJ_ONE: */
/*             return 1; */
/*         case DATA_OBJ_BYTE: */
/*             return 2; */
/*         case DATA_OBJ_WORD: */
/*             return 3; */
/*         case DATA_OBJ_DWORD: */
/*             return 5; */
/*         case DATA_OBJ_STRING: { */
/*             uint32_t i = 0; */
/*             while (data_encoding[++i]); */
/*             return i + 1; */
/*         case DATA_OBJ_BUFFER: */
/*             return 1 + get_pkt_len(&data_encoding[1]); */
/*         case DATA_OBJ_PACKAGE: */
/*             return 1 + get_pkt_len(&data_encoding[1]); */
/*         } */
/*     } */
/*     return 0; */
/* } */

/* // get length of bytes specifing length of data in Name Object */
/* uint32_t get_name_data_len_len(uint8_t *data_encoding) */
/* { */
/*     switch (data_encoding[0]) { */
/*         case DATA_OBJ_ZERO: */
/*         case DATA_OBJ_ONE: */
/*         case DATA_OBJ_BYTE: */
/*         case DATA_OBJ_WORD: */
/*         case DATA_OBJ_DWORD: */
/*             return 1; */
/*         case DATA_OBJ_STRING: { */
/*             uint32_t i = 0; */
/*             while (data_encoding[++i]); */
/*             return 1; */
/*         } */
/*         case DATA_OBJ_BUFFER: */
/*             return 1 + get_pktlen_bytes(&data_encoding[1]); */
/*         case DATA_OBJ_PACKAGE: */
/*             return 1 + get_pktlen_bytes(&data_encoding[1]); */
/*     } */
/*     return 0; */
/* } */

/* uint32_t get_integer_data(uint8_t *data_encoding) */
/* { */
/*     switch (data_encoding[0]) { */
/*         case DATA_OBJ_ZERO: */
/*             return 0; */
/*         case DATA_OBJ_ONE: */
/*             return 1; */
/*         case DATA_OBJ_BYTE: */
/*             return data_encoding[1]; */
/*         case DATA_OBJ_WORD: */
/*             return (data_encoding[2] << 8) + data_encoding[1]; */
/*         case DATA_OBJ_DWORD: */
/*             return (data_encoding[3] << 24) + (data_encoding[2] << 16) + (data_encoding[1] << 8) + data_encoding[0]; */
/*         default: { */
/*             sddf_dprintf("Not implemented data type: 0x%x\n", data_encoding[0]); */
/*         } */
/*     } */
/*     return 0; */
/* } */

/* // Parse the compressed EISA ID to readable characters */
/* void read_eisa_id(uint8_t *eisa_id_bytes, char *eisa_id_str) { */

/*     sddf_dprintf("bytes: %02x %02x\n", eisa_id_bytes[0], eisa_id_bytes[1]); */
/*     // Combine the first two bytes in little-endian */
/*     uint16_t char_word = (eisa_id_bytes[0] << 8) | eisa_id_bytes[1]; */

/*     // Extract the 3 characters */
/*     // Bit mapping: 0-4 (Char 3), 5-9 (Char 2), 10-14 (Char 1) */
/*     eisa_id_str[0] = (char)(((char_word >> 10) & 0x1F) + 0x40); */
/*     eisa_id_str[1] = (char)(((char_word >> 5)  & 0x1F) + 0x40); */
/*     eisa_id_str[2] = (char)((char_word & 0x1F) + 0x40); */

/*     // Extract four Hex ID from the last two bytes */
/*     /\* uint8_t hex_hi = bytes[2]; *\/ */
/*     eisa_id_str[3] = (char)(HEX_TO_CHAR(eisa_id_bytes[2] >> 4)); */
/*     eisa_id_str[4] = (char)(HEX_TO_CHAR(eisa_id_bytes[2] & 0xF)); */
/*     /\* uint8_t hex_lo = bytes[3]; *\/ */
/*     eisa_id_str[5] = (char)(HEX_TO_CHAR(eisa_id_bytes[3] >> 4)); */
/*     eisa_id_str[6] = (char)(HEX_TO_CHAR(eisa_id_bytes[3] & 0xF)); */

/*     eisa_id_str[7] = '\0'; */
/* } */

/* bool match_path(char *path_a, char *path_b) */
/* { */
/*     uint8_t i = 0; */
/*     while (path_a[i] == '\\') i++; */
/*     uint8_t j = 0; */
/*     while (path_b[j] == '\\') j++; */
/*     sddf_dprintf("path_a: %s, i = %d, path_b: %s, j = %d\n", path_a, i, path_b, j); */
/*     return !strcmp(&path_a[i], &path_b[j]); */
/* } */

/* // Section 6.4 */
/* void parse_resource_data(uint8_t *resource_data, uint32_t buffer_size) */
/* { */

/*     for (uint32_t i = 0; i < buffer_size;) { */
/*         uint32_t descriptor_type = resource_data[i]; */
/*         uint32_t descriptor_len = (resource_data[i] & 0x80) ? ((resource_data[i+2] << 8) + resource_data[i+1] + 3) : ((resource_data[i] & 0x7) + 1); */
/*         switch (descriptor_type) { */
/*             case WORD_AS_DESCRIPTOR: { */
/*                 acpi_word_address_space_t *word_as = (acpi_word_address_space_t *)&resource_data[i]; */
/*                 sddf_dprintf("  =========\n"); */
/*                 switch (word_as->resource_type) { */
/*                     case 0: { sddf_dprintf("  type: Word Memory\n"); break; } */
/*                     case 1: { sddf_dprintf("  type: Word I/O\n"); break; } */
/*                     case 2: { sddf_dprintf("  type: Word Bus Number Range\n"); break; } */
/*                 } */
/*                 sddf_dprintf("  granularity: 0x%x\n", word_as->granularity); */
/*                 sddf_dprintf("  min_addr: 0x%x\n", word_as->min_address); */
/*                 sddf_dprintf("  max_addr: 0x%x\n", word_as->max_address); */
/*                 sddf_dprintf("  translation: 0x%x\n", word_as->translation); */
/*                 sddf_dprintf("  addr_len: 0x%x\n", word_as->address_length); */
/*                 break; */
/*             } */
/*             case IO_PORT_DESCRIPTOR: { */
/*                 acpi_io_port_t *io_port = (acpi_io_port_t *)&resource_data[i]; */
/*                 sddf_dprintf("  =========\n"); */
/*                 sddf_dprintf("  type: I/O Port\n"); */
/*                 sddf_dprintf("  min_addr: 0x%x\n", io_port->min_address); */
/*                 sddf_dprintf("  max_addr: 0x%x\n", io_port->max_address); */
/*                 sddf_dprintf("  alignment: 0x%x\n", io_port->alignment); */
/*                 sddf_dprintf("  addr_len: 0x%x\n", io_port->address_length); */
/*                 break; */
/*             } */
/*             case DWORD_AS_DESCRIPTOR: { */
/*                 acpi_dword_address_space_t *dword_as = (acpi_dword_address_space_t *)&resource_data[i]; */
/*                 sddf_dprintf("  =========\n"); */
/*                 switch (dword_as->resource_type) { */
/*                     case 0: { sddf_dprintf("  type: DWord Memory\n"); break; } */
/*                     case 1: { sddf_dprintf("  type: DWord I/O\n"); break; } */
/*                     case 2: { sddf_dprintf("  type: DWord Bus Number Range\n"); break; } */
/*                 } */

/*                 sddf_dprintf("  granularity: 0x%x\n", dword_as->granularity); */
/*                 sddf_dprintf("  min_addr: 0x%x\n", dword_as->min_address); */
/*                 sddf_dprintf("  max_addr: 0x%x\n", dword_as->max_address); */
/*                 sddf_dprintf("  translation: 0x%x\n", dword_as->translation); */
/*                 sddf_dprintf("  addr_len: 0x%x\n", dword_as->address_length); */
/*                 break; */
/*             } */
/*             case QWORD_AS_DESCRIPTOR: { */
/*                 acpi_qword_address_space_t *qword_as = (acpi_qword_address_space_t *)&resource_data[i]; */
/*                 sddf_dprintf("  =========\n"); */
/*                 switch (qword_as->resource_type) { */
/*                     case 0: { sddf_dprintf("  type: QWord Memory\n"); break; } */
/*                     case 1: { sddf_dprintf("  type: QWord I/O\n"); break; } */
/*                     case 2: { sddf_dprintf("  type: QWord Bus Number Range\n"); break; } */
/*                 } */

/*                 sddf_dprintf("  granularity: 0x%lx\n", qword_as->granularity); */
/*                 sddf_dprintf("  min_addr: 0x%lx\n", qword_as->min_address); */
/*                 sddf_dprintf("  max_addr: 0x%lx\n", qword_as->max_address); */
/*                 sddf_dprintf("  translation: 0x%lx\n", qword_as->translation); */
/*                 sddf_dprintf("  addr_len: 0x%lx\n", qword_as->address_length); */
/*                 break; */
/*             } */
/*             default: { */
/*                 sddf_dprintf("Resource type 0x%02x parsing is not implemented\n", descriptor_type); */
/*             } */
/*         } */
/*         i = i + descriptor_len; */
/*     } */
/* } */

/* bool extract_crs(uint8_t *resource_data, uint32_t data_len, char *path_name, uint32_t path_len) */
/* { */
/*     for (uint8_t i = 0; i < pci_resources.num_bridges; i++) { */
/*         sddf_dprintf("----------\n"); */
/*         if (match_path(pci_resources.bridges[i].path_name, path_name)) { */
/*             sddf_dprintf("matched path: %s\n", path_name); */
/*             uint32_t buffer_size = get_integer_data(resource_data); */
/*             uint32_t buffer_size_bytes = get_name_data_len(resource_data); */
/*             sddf_dprintf("buffer_size: %d, buffer_size_bytes: %d\n", buffer_size, buffer_size_bytes); */
/*             parse_resource_data(&resource_data[buffer_size_bytes], buffer_size); */
/*         } */

/*     } */
/*     return false; */
/* } */

/* void save_if_apic_routing_table(uint8_t *name_object, char *name_str) */
/* { */
/*     // Check if package object */
/*     if (name_object[0] != 0x12) return; */

/*     sddf_dprintf("Package Object\n"); */
/*     uint32_t pkt_len = get_pkt_len(&name_object[1]); */
/*     uint32_t pkt_len_bytes = get_pktlen_bytes(&name_object[1]); */
/*     uint32_t num_elements = name_object[1 + pkt_len_bytes]; */
/*     sddf_dprintf("pkt_len: %d, pkt_len_bytes: %d, num_elements: 0x%x\n", pkt_len, pkt_len_bytes, num_elements); */

/*     if (name_object[2 + pkt_len_bytes] != 0x12) return; */

/*     for (int i = 2 + pkt_len_bytes; i < pkt_len;) { */
/*         // Check if element is also Package Object */
/*         if (name_object[i] != 0x12) return; */

/*         uint32_t element_pkt_len = get_pkt_len(&name_object[i + 1]); */
/*         uint32_t element_pkt_len_bytes = get_pktlen_bytes(&name_object[i + 1]); */
/*         uint32_t element_num_elements = name_object[i + 1 + element_pkt_len_bytes]; */

/*         // Check if num of elements is 4 */
/*         if (element_num_elements != 4) return; */

/*         // Parse address, i.e. PCI slot */
/*         uint32_t arg_idx = i + 2 + element_pkt_len_bytes; */
/*         uint32_t element_1 = get_integer_data(&name_object[arg_idx]); */

/*         // Parse PIN */
/*         arg_idx = arg_idx + get_name_data_len(&name_object[arg_idx]); */
/*         uint32_t element_2 = get_integer_data(&name_object[arg_idx]); */

/*         // Parse Source, i.e. GSI number */
/*         arg_idx = arg_idx + get_name_data_len(&name_object[arg_idx]); */
/*         char name_str[20]; */
/*         uint32_t source_len = get_name_string(&name_object[arg_idx], name_str); */

/*         // Parse Source Index, i.e. index in I/O APIC */
/*         arg_idx = arg_idx + source_len; */
/*         uint32_t element_4 = get_integer_data(&name_object[arg_idx]); */
/*         sddf_dprintf("{ 0x%X, 0x%x, %s, 0x%x}\n", element_1, element_2, name_str, element_4); */

/*         i = i + 1 + element_pkt_len; */
/*     } */
/* } */

/* void parse_method_definition(uint8_t *func_def, uint32_t def_len) */
/* { */
/*     // Skip 1 byte for Method Flags */
/*     /\* for (int i = 1; i < def_len;) { *\/ */
/*     /\*     switch (func_dev[i]) { *\/ */
/*     /\*         case IF_OP: { *\/ */
/*     /\*             uint32_t pkt_len = get_pkt_len(&func_def[i+1]); *\/ */
/*     /\*             sddf_dprintf("** METHOD If: pkt_len: %u\n", pkt_len); *\/ */
/*     /\*         } *\/ */
/*     /\*         case *\/ */
/*     /\*     } *\/ */
/*     /\* } *\/ */
/* } */

/* uint32_t extract_device_resources(uint8_t *cur_obj, uint32_t obj_len, char *path_name, uint32_t path_len) */
/* { */
/*     sddf_dprintf("#######################start extract##########\n"); */
/*     char name_str[20]; */
/*     uint32_t arg_idx; */
/*     uint16_t ext_op_prefix = 0; */
/*     for (int i = 0; i < obj_len;) { */
/*         sddf_dprintf("base addr: 0x%lx, obj_len: %u, byte address: 0x%lx, i: 0x%x\n", (uintptr_t)cur_obj, obj_len, (uintptr_t)&(cur_obj[i]), i); */
/*         switch (ext_op_prefix | cur_obj[i]) { */
/*             case SCOPE_OP: { */
/*                 sddf_dprintf("== SCOPE_OP\n"); */

/*                 // pktLength Encoding */
/*                 // TODO: remove this by something like advance() */
/*                 arg_idx = i + 1; */
/*                 uint32_t pkt_len = get_pkt_len(&cur_obj[arg_idx]); */
/*                 sddf_dprintf("pkt_len: %u\n", pkt_len); */

/*                 // Name String */
/*                 arg_idx = arg_idx + get_pktlen_bytes(&cur_obj[arg_idx]); */
/*                 sddf_dprintf("path_len: %d\n", path_len); */
/*                 uint32_t name_len = get_name_string(&cur_obj[arg_idx], &path_name[path_len]); */
/*                 sddf_dprintf("current path: %s, len: %d\n", path_name, path_len + name_len); */

/*                 // Parse objects inside the scope */
/*                 arg_idx = arg_idx + name_len; */
/*                 sddf_dprintf("===1 path len: %d\n", path_len); */
/*                 extract_device_resources(&cur_obj[arg_idx], pkt_len - (arg_idx - i - 1), path_name, path_len + name_len); */
/*                 sddf_dprintf("===2 path len: %d\n", path_len); */

/*                 i = i + 1 + pkt_len; */
/*                 break; */
/*             } */
/*             case NAME_OP: { */
/*                 sddf_dprintf("== NAME_OP\n"); */
/*                 uint32_t name_len = get_name_string(&cur_obj[i + 1], name_str); */
/*                 sddf_dprintf("name_str: %s, len: %d\n", name_str, name_len); */
/*                 uint32_t data_len = get_name_data_len(&cur_obj[i + 1 + name_len]); */
/*                 sddf_dprintf("name object data len: %d\n", data_len); */
/*                 if (!strcmp(name_str, "_HID")) { // Add entry if it's a PCI bridge */
/*                     char eisa_id[8]; */
/*                     if (data_len == 5) { // Compressed EISA ID */
/*                         read_eisa_id(&cur_obj[i + 1 + name_len + 1], eisa_id); */
/*                     } else { */
/*                         memcpy(eisa_id, &cur_obj[i + 1 + name_len + 1], data_len); */
/*                     } */
/*                     sddf_dprintf("Decoded EISA ID: %s, path: %s\n", eisa_id, path_name); */
/*                     if (!strcmp(eisa_id, "PNP0A08")) { */
/*                         sddf_dprintf("Found a PCI device\n"); */
/*                         memcpy(pci_resources.bridges[pci_resources.num_bridges].path_name, path_name, path_len); */
/*                         pci_resources.bridges[pci_resources.num_bridges].path_len = path_len; */
/*                         pci_resources.num_bridges++; */
/*                     } */
/*                 } else if (!strcmp(name_str, "_CRS")) { // Save CRS */
/*                     sddf_dprintf("_CRS for path: %s\n", path_name); */
/*                     uint32_t datalen_len = get_name_data_len_len(&cur_obj[i + 1 + name_len]); */
/*                     sddf_dprintf("length of data length: %d\n", datalen_len); */
/*                     extract_crs(&cur_obj[i + 1 + name_len + datalen_len], data_len - datalen_len, path_name, path_len); */
/*                 } else { */
/*                     save_if_apic_routing_table(&cur_obj[i + 1 + name_len], name_str); */
/*                 } */
/*                 i = i + 1 + name_len + data_len; */
/*                 break; */
/*             } */
/*             case METHOD_OP: { */
/*                 sddf_dprintf("== METHOD_OP\n"); */
/*                 uint32_t pkt_len = get_pkt_len(&cur_obj[i+1]); */
/*                 sddf_dprintf("pkt_len: %u\n", pkt_len); */

/*                 uint32_t arg_idx = i + 1 + get_pktlen_bytes(&cur_obj[i+1]); */
/*                 uint32_t name_len = get_name_string(&cur_obj[arg_idx], name_str); */
/*                 sddf_dprintf("name_str: %s, len: %d\n", name_str, name_len); */

/*                 arg_idx = arg_idx + name_len; */
/*                 if (!strcmp(name_str, "_PRT")) { */
/*                     /\* parse_method_definition(&cur_obj[arg_idx]); *\/ */
/*                 } */

/*                 i = i + 1 + pkt_len; */
/*                 break; */
/*             } */
/*             case EXT_OP_PREFIX: { */
/*                 ext_op_prefix = EXT_OP_PREFIX << 8; */
/*                 i = i + 1; */
/*                 break; */
/*             } */
/*             case DEVICE_OP: { */
/*                 sddf_dprintf("== DEVICE_OP\n"); */

/*                 // pktLength Encoding */
/*                 arg_idx = i + 1; */
/*                 uint32_t pkt_len = get_pkt_len(&cur_obj[arg_idx]); */
/*                 sddf_dprintf("pkt_len: %u\n", pkt_len); */

/*                 // Name String */
/*                 arg_idx = arg_idx + get_pktlen_bytes(&cur_obj[arg_idx]); */
/*                 uint32_t name_len = get_name_string(&cur_obj[arg_idx], &path_name[path_len]); */
/*                 sddf_dprintf("current path: %s, len: %d\n", path_name, path_len + name_len); */

/*                 // Parse objects inside the scope */
/*                 arg_idx = arg_idx + name_len; */
/*                 sddf_dprintf("===3 path: %s, path len: %d, name_len: %d\n", path_name, path_len, name_len); */
/*                 extract_device_resources(&cur_obj[arg_idx], pkt_len - (arg_idx - i - 1), path_name, path_len + name_len); */
/*                 sddf_dprintf("===4 path len: %d\n", path_len); */

/*                 ext_op_prefix = 0; */
/*                 i = i + 1 + pkt_len; */
/*                 break; */
/*             } */
/*             default: { */
/*                 sddf_dprintf("Object Type '0x%02x' cannot be parsed.\n", ext_op_prefix | cur_obj[i]); */
/*                 i = obj_len; */
/*                 break; */
/*             } */
/*         } */
/*         sddf_dprintf("i: 0x%x, obj_len: 0x%x\n", i, obj_len); */
/*     } */
/*     sddf_dprintf("===5 path len: %d\n", path_len); */
/*     return 0; */
/* } */

typedef struct {
    uint8_t* start;
    uint8_t* current;
} scanner_t;

typedef struct aml_object {
    const uint8_t *start;
    struct aml_object *parent;  // parent
    struct aml_object *child;   // first child object
    struct aml_object *next;    // siblings
    char name[5];    // Name Segment
    enum aml_encoding_value op_code;
} aml_object_t;

typedef struct aml_object_pool {
    aml_object_t *next;
    aml_object_t *end;
} aml_object_pool_t;

void scan_objects(aml_object_t *parent, uint8_t *next_parent_start);
void print_object_tree(aml_object_t *node, uint8_t depth);

extern uintptr_t aml_object_pool_start;
extern scanner_t scanner;
extern aml_object_pool_t object_pool;
extern aml_object_t object_root;
extern pci_resources_t pci_resources;
