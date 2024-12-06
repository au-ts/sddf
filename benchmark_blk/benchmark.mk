#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# Include this snippet in your project Makefile to build
# the benchmark.elf and idle.elf programs.
#
BENCH_OBJS := benchmark_blk/benchmark_blk.o
IDLE_OBJS := benchmark_blk/idle.o
LIBUTIL_DBG := libsddf_util_debug.a
LIBUTIL := libsddf_util.a

${BENCH_OBJS} ${IDLE_OBJS}: ${CHECK_FLAGS_BOARD_MD5} |benchmark_blk benchmark_blk.o idle.o

benchmark_blk.o: ${SDDF}/benchmark_blk/benchmark_blk.c
	${CC} ${CFLAGS} ${CFLAGS_blk} -o benchmark_blk/$@ -c $<

idle.o: ${SDDF}/benchmark_blk/idle.c
	${CC} ${CFLAGS} ${CFLAGS_blk} -o benchmark_blk/$@ -c $<

benchmark_blk:
	mkdir -p benchmark_blk


benchmark_blk.elf: $(BENCH_OBJS) ${LIBUTIL}
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

idle.elf: $(IDLE_OBJS) ${LIBUTIL_DBG}
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@
