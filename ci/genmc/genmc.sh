#!/bin/bash
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

cd "$(dirname "$0")/../.."

set -ev

for i in `seq 0 3`; do
  export CMD="genmc --disable-estimation --disable-mm-detector --v1 -- -I./ci/genmc -I./include"

  if [ $(( i % 2 )) -eq 1 ]; then
    export CMD="$CMD -DCONFIG_ENABLE_SMP_SUPPORT=1"
  fi

  if [ $(( i / 2 )) -eq 1 ]; then
    export CMD="$CMD -DCONFIG_DEBUG_BUILD=1"
  fi

  $CMD ./ci/genmc/serial/test1.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=2 -DCONSUMER=2 ./ci/genmc/serial/test1.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=4 -DCONSUMER=4 ./ci/genmc/serial/test1.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=6 -DCONSUMER=6 ./ci/genmc/serial/test1.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=8 -DCONSUMER=8 ./ci/genmc/serial/test1.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=4 -DCONSUMER=4 ./ci/genmc/serial/test1.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=6 -DCONSUMER=6 ./ci/genmc/serial/test1.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=7 -DCONSUMER=6 ./ci/genmc/serial/test1.c
done

for i in `seq 0 3`; do
  export CMD="genmc --disable-estimation --disable-mm-detector --v1 -- -I./ci/genmc -I./include"

  if [ $(( i % 2 )) -eq 1 ]; then
    export CMD="$CMD -DCONFIG_ENABLE_SMP_SUPPORT=1"
  fi

  if [ $(( i / 2 )) -eq 1 ]; then
    export CMD="$CMD -DCONFIG_DEBUG_BUILD=1"
  fi

  $CMD ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=2 -DCONSUMER=2 -DBATCH_SIZE=1 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=2 -DCONSUMER=2 -DBATCH_SIZE=2 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=4 -DCONSUMER=4 -DBATCH_SIZE=1 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=4 -DCONSUMER=4 -DBATCH_SIZE=2 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=6 -DCONSUMER=6 -DBATCH_SIZE=1 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=6 -DCONSUMER=6 -DBATCH_SIZE=2 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=8 -DCONSUMER=8 -DBATCH_SIZE=1 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=8 -DCONSUMER=8 -DBATCH_SIZE=2 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=4 -DCONSUMER=4 -DBATCH_SIZE=1 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=4 -DCONSUMER=4 -DBATCH_SIZE=2 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=4 -DCONSUMER=4 -DBATCH_SIZE=3 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=4 -DCONSUMER=4 -DBATCH_SIZE=4 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=6 -DCONSUMER=6 -DBATCH_SIZE=3 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=6 -DCONSUMER=6 -DBATCH_SIZE=4 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=7 -DCONSUMER=6 -DBATCH_SIZE=3 ./ci/genmc/serial/test2.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=7 -DCONSUMER=6 -DBATCH_SIZE=4 ./ci/genmc/serial/test2.c
done

for i in `seq 0 3`; do
  export CMD="genmc --disable-estimation --disable-mm-detector --v1 -- -I./ci/genmc -I./include"

  if [ $(( i % 2 )) -eq 1 ]; then
    export CMD="$CMD -DCONFIG_ENABLE_SMP_SUPPORT=1"
  fi

  if [ $(( i / 2 )) -eq 1 ]; then
    export CMD="$CMD -DCONFIG_DEBUG_BUILD=1"
  fi

  $CMD ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=2 -DCONSUMER=2 -DBATCH_SIZE=1 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=4 -DCONSUMER=2 -DBATCH_SIZE=2 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=4 -DCONSUMER=4 -DBATCH_SIZE=1 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=6 -DCONSUMER=6 -DBATCH_SIZE=1 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=6 -DCONSUMER=3 -DBATCH_SIZE=2 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=8 -DCONSUMER=8 -DBATCH_SIZE=1 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=8 -DCONSUMER=4 -DBATCH_SIZE=2 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=4 -DCONSUMER=4 -DBATCH_SIZE=1 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=4 -DCONSUMER=2 -DBATCH_SIZE=2 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=4 -DCONSUMER=1 -DBATCH_SIZE=3 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=4 -DCONSUMER=1 -DBATCH_SIZE=4 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=6 -DCONSUMER=2 -DBATCH_SIZE=3 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=6 -DCONSUMER=1 -DBATCH_SIZE=4 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=7 -DCONSUMER=2 -DBATCH_SIZE=3 ./ci/genmc/serial/test3.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=7 -DCONSUMER=1 -DBATCH_SIZE=4 ./ci/genmc/serial/test3.c
done
