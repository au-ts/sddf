#if defined(__clang__)
#pragma clang diagnostic ignored "-Wparentheses"

  /* placing code in section(text) does not mark it executable with Clang. */
#undef LIBCO_MPROTECT
#define LIBCO_MPROTECT
#endif

#if defined(__clang__) || defined(__GNUC__)
#if defined(__amd64__)
#include "amd64.c"
#elif defined(__arm__)
#include "arm.c"
#elif defined(__aarch64__)
#include "aarch64.c"
#elif defined(__riscv) && __riscv_xlen == 64
#if !defined(__riscv_flen)
#include "riscv64.c"
#elif defined(__riscv_flen) && __riscv_flen == 64
#include "riscv64.c"
#elif defined(__riscv_flen) && __riscv_flen != 64
#error "libco: err1: unsupported RISC-V processor"
#endif
#else
#error "libco: unsupported processor, compiler or operating system"
#endif
#else
#error "libco: unsupported processor, compiler or operating system"
#endif
