#!/bin/bash
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

cd "$(dirname "$0")/../.."

set -ev

for i in `seq 0 1`; do
  export CMD="genmc --disable-estimation --disable-mm-detector --v1 -- -I./ci/genmc -I./include"

  if [ "$i" -eq 1 ]; then
    export CMD="$CMD -DCONFIG_ENABLE_SMP_SUPPORT=1"
  fi

  $CMD ./ci/genmc/network/test1.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=2 -DCONSUMER=2 ./ci/genmc/network/test1.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=4 -DCONSUMER=4 ./ci/genmc/network/test1.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=6 -DCONSUMER=6 ./ci/genmc/network/test1.c

  $CMD -DQUEUE_SIZE=2 -DPRODUCER=8 -DCONSUMER=8 ./ci/genmc/network/test1.c

  $CMD -DQUEUE_SIZE=3 -DPRODUCER=4 -DCONSUMER=4 ./ci/genmc/network/test1.c

  $CMD -DQUEUE_SIZE=3 -DPRODUCER=6 -DCONSUMER=6 ./ci/genmc/network/test1.c

  $CMD -DQUEUE_SIZE=3 -DPRODUCER=7 -DCONSUMER=7 ./ci/genmc/network/test1.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=4 -DCONSUMER=4 ./ci/genmc/network/test1.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=6 -DCONSUMER=6 ./ci/genmc/network/test1.c

  $CMD -DQUEUE_SIZE=4 -DPRODUCER=7 -DCONSUMER=6 ./ci/genmc/network/test1.c
done
