#include <microkit.h>
#include <os/sddf.h>
#include <sddf/util/cache.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>

void ffisddf_irq_ack(unsigned char *c, long clen, unsigned char *a, long alen) {
    sddf_irq_ack(clen);
}

void ffisddf_notify(unsigned char *c, long clen, unsigned char *a, long alen) {
    sddf_notify(clen);
}

void ffisddf_deferred_irq_ack(unsigned char *c, long clen, unsigned char *a, long alen) {
    sddf_deferred_irq_ack(clen);
}

void ffisddf_deferred_notify(unsigned char *c, long clen, unsigned char *a, long alen) {
    sddf_deferred_notify(clen);
}

#if defined(CONFIG_ARCH_X86_64)
void ffimicrokit_x86_ioport_write_8(unsigned char *c, long clen, unsigned char *a, long alen) {
    microkit_x86_ioport_write_8(clen, (seL4_Word) c, (seL4_Word) a);
}

void ffimicrokit_x86_ioport_read_8(unsigned char *c, long clen, unsigned char *a, long alen) {
    seL4_Uint8 ret = microkit_x86_ioport_read_8(clen, (seL4_Word) a);
    *(seL4_Uint8 *)c = ret; 
}
#endif

void fficache_clean(unsigned char *c, long clen, unsigned char *a, long alen) {
    cache_clean((unsigned long) c, (unsigned long) a);
}

void fficache_clean_and_invalidate(unsigned char *c, long clen, unsigned char *a, long alen) {
    cache_clean_and_invalidate((unsigned long) c, (unsigned long) a);
}

void ffiTHREAD_MEMORY_RELEASE(unsigned char *c, long clen, unsigned char *a, long alen) {
    THREAD_MEMORY_RELEASE();
}

void ffiTHREAD_MEMORY_ACQUIRE(unsigned char *c, long clen, unsigned char *a, long alen) {
    THREAD_MEMORY_ACQUIRE();
}

void ffidebug_print(unsigned char *c, long clen, unsigned char *a, long alen) {
    /* clen = debug value to print, alen = context/location id */
    sddf_dprintf("[DEBUG] Location %ld: Value = %ld (0x%lx)\n", alen, clen, clen);
}

void ffifence_seq_cst(unsigned char *c, long clen, unsigned char *a, long alen) {
    __atomic_thread_fence(__ATOMIC_SEQ_CST);
}
