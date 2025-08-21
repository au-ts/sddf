/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

// 1. Get all the loadabale segments
// 2. If it is writable, basically expand the segment and do a memcpy

#include <microkit.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/util/printf.h>
#include <sddf/benchmark/sel4bench.h>
#include "vspace.h"

__attribute__((__section__(".serial_client_config"))) serial_client_config_t config;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

__attribute__((__section__(".child_elf"))) char child_elf[1024 * 1024 * 2];

char *magic = "\x7F""ELF";

typedef struct
{
  uint32_t    p_type;            /* Segment type */
  uint32_t    p_flags;        /* Segment flags */
  uint64_t    p_offset;        /* Segment file offset */
  uint64_t    p_vaddr;        /* Segment virtual address */
  uint64_t    p_paddr;        /* Segment physical address */
  uint64_t    p_filesz;        /* Segment size in file */
  uint64_t    p_memsz;        /* Segment size in memory */
  uint64_t    p_align;        /* Segment alignment */
} Elf64_Phdr;

typedef struct {
    unsigned char e_ident[16]; /* ELF identification */
    uint16_t e_type;           /* Object file type */
    uint16_t e_machine;        /* Machine type */
    uint32_t e_version;        /* Object file version */
    uint64_t e_entry;          /* Entry point address */
    uint64_t e_phoff;          /* Program header offset */
    uint64_t e_shoff;          /* Section header offset */
    uint32_t e_flags;          /* Processor-specific flags */
    uint16_t e_ehsize;         /* ELF header size */
    uint16_t e_phentsize;      /* Size of program header entry */
    uint16_t e_phnum;          /* Number of program header entries */
    uint16_t e_shentsize;      /* Size of section header entry */
    uint16_t e_shnum;          /* Number of section header entries */
    uint16_t e_shstrndx;       /* Section name string table index */
} Elf64_Ehdr;

#define PT_LOAD 1

#define PF_X        (1 << 0)    /* Segment is executable */
#define PF_W        (1 << 1)    /* Segment is writable */
#define PF_R        (1 << 2)    /* Segment is readable */
#define PF_MASKOS   0x0ff00000  /* OS-specific */
#define PF_MASKPROC 0xf0000000  /* Processor-specific */

uint64_t small_mapping_mr;
uint64_t large_mapping_mr;

void reload_elf() {
    Elf64_Ehdr *hdr = (Elf64_Ehdr *)child_elf;
    // sddf_printf("e_phnum: %lu\n", hdr->e_phnum);
    // sddf_printf("e_shnum: %lu\n", hdr->e_shnum);
    // sddf_printf("e_entry: %lu\n", hdr->e_entry);
    // sddf_printf("version: %lu\n", hdr->e_version);

    for (int i = 0; i < hdr->e_phnum; i++) {
        size_t phent_start = hdr->e_phoff + (i * hdr->e_phentsize);
        Elf64_Phdr *phent = (Elf64_Phdr *)(child_elf + phent_start);

        if (phent->p_type != PT_LOAD || (phent->p_flags & PF_W) == 0) {
            continue;
        }

        sddf_printf("INFO: dealing with loadable and writable segment\n");

        size_t segment_start = phent->p_offset;
        char *segment_file_data = child_elf + segment_start;
        sddf_printf("INFO: segment memsz %lu, filesz: %lu\n", phent->p_memsz, phent->p_filesz);

        // Write out filesz bytes first
        sddf_dprintf("INFO: writing %d filesz bytes from 0x%lx\n", phent->p_filesz, phent->p_vaddr);
        libvspace_write_bytes(0, phent->p_vaddr, segment_file_data, phent->p_filesz);
        // Then pad filesz bytes with zeroes until we reach memsz
        size_t num_zeroes = phent->p_memsz - phent->p_filesz;
        sddf_dprintf("INFO: writing %d zeroes from 0x%lx\n", num_zeroes, phent->p_vaddr + phent->p_filesz);
        libvspace_write_bytes(0, phent->p_vaddr + phent->p_filesz, NULL, phent->p_memsz - phent->p_filesz);
    }
    seL4_Word sp = 0x0000010000000000;

    seL4_Error err;
    seL4_UserContext ctxt = {0};
    ctxt.pc = hdr->e_entry;
    ctxt.sp = sp;
    err = seL4_TCB_WriteRegisters(
              BASE_TCB_CAP + 0,
              seL4_False,
              0, /* No flags */
              2, /* writing 2 register */
              &ctxt
          );
}

void init(void)
{
    assert(serial_config_check_magic(&config));

    serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);

    serial_putchar_init(config.tx.id, &tx_queue_handle);
    sddf_printf("PARENT|INFO: starting\n");

    for (int i = 0; i < 4; i++) {
        assert(child_elf[i] == magic[i]);
    }

    libvspace_set_small_mapping_region(small_mapping_mr);
    libvspace_set_large_mapping_region(large_mapping_mr);

#ifdef CONFIG_ENABLE_BENCHMARKS
    sel4bench_init();
#endif

    sddf_printf("PARENT|INFO: init done\n");
    // fault(0, microkit_msginfo_new(0, 0), NULL);
}

void notified(microkit_channel ch)
{
}

int reload_count = 0;

seL4_Bool fault(microkit_child child, microkit_msginfo msginfo, microkit_msginfo *reply_msginfo)
{
    if (reload_count < 100) {
        sddf_printf("PARENT|INFO: reloading child ELF due to fault\n");

#ifdef CONFIG_ENABLE_BENCHMARKS
        uint64_t pre;
        uint64_t post;

        SEL4BENCH_READ_CCNT(pre);
#endif
        reload_elf();
#ifdef CONFIG_ENABLE_BENCHMARKS
        SEL4BENCH_READ_CCNT(post);

        sddf_printf("[%d] %lu\n", reload_count, post - pre);
#endif

        reload_count += 1;
    } else {
        microkit_pd_stop(0);
    }

    return seL4_True;
}
