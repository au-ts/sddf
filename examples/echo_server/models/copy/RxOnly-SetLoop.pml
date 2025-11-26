// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

// COMPONENTS: Client, copy, virt rx
// OUTCOME: Deadlock freedom in 7.76 seconds

#define QUEUE_CAPACITY 2

typedef queue {
    chan notification = [1] of {bit};
    bit flag;
    unsigned head : 2;
    unsigned tail : 2;
}

queue CPY_RX_free;
queue CPY_RX_active;
queue CLT_RX_free;
queue CLT_RX_active;

#define LEN(q)          (q.tail - q.head)
#define EMPTY(q)        (q.tail - q.head == 0)
#define FULL(q)         (q.tail - q.head == QUEUE_CAPACITY)

#define TRANSFER(from, to) { \
    d_step { \
        from.head++; \
        to.tail++; \
    } \
}

#define REMOVE(from, stored) { \
    d_step { \
        from.head++; \
        stored++; \
    } \
}

#define INSERT(to, stored) { \
    d_step { \
        to.tail++; \
        stored--; \
    } \
}

init priority 2 {
    CLT_RX_free.tail = 2;
    CLT_RX_active.flag = 1;

    CPY_RX_active.flag = 1;
    CPY_RX_free.flag = 1;
}

active proctype CLIENT() priority 1 {
    bit notify_rx;
    do
    :: skip ->
        if
        :: CLT_RX_active.notification ? 1 ->
            work_clt: ;
            do
            :: !EMPTY(CLT_RX_active) ->
                TRANSFER(CLT_RX_active, CLT_RX_free);
                notify_rx = 1;
            :: else -> break;
            od
        fi;

        CLT_RX_active.flag = 1;

        if
        :: !EMPTY(CLT_RX_active) ->
            CLT_RX_active.flag = 0;
            goto work_clt;
        :: else;
        fi

        if
        :: notify_rx && CLT_RX_free.flag && !(CLT_RX_free.notification ?? [1]) ->
            notify_rx = 0;
            CLT_RX_free.flag = 0;
            CLT_RX_free.notification ! 1;
        :: else;
        fi;
    od;
}

active proctype COPY() priority 1 {
    do
    :: CPY_RX_active.notification ? 1 -> goto work_copy_start;
    :: CLT_RX_free.notification ? 1 ->
        work_copy_start: ;
        bit enqueued = 0;
        work_copy: ;
        do
        :: !EMPTY(CPY_RX_active) && !EMPTY(CLT_RX_free) ->
            TRANSFER(CPY_RX_active, CPY_RX_free);
            TRANSFER(CLT_RX_free, CLT_RX_active);
            enqueued = 1;
        :: else -> break;
        od;

        CPY_RX_active.flag = 1;

        if
        :: !EMPTY(CPY_RX_active) -> CLT_RX_free.flag = 1;
        :: else -> CLT_RX_free.flag = 0;
        fi;

        if
        :: !EMPTY(CPY_RX_active) && !EMPTY(CLT_RX_free) ->
            CPY_RX_active.flag = 0;
            CLT_RX_free.flag = 0;
            goto work_copy;
        :: else;
        fi

        if
        :: enqueued && CLT_RX_active.flag && !(CLT_RX_active.notification ?? [1]) ->
            CLT_RX_active.flag = 0;
            CLT_RX_active.notification ! 1;
        :: else;
        fi;

        if
        :: enqueued && CPY_RX_free.flag && !(CPY_RX_free.notification ?? [1]) ->
            CPY_RX_free.flag = 0;
            CPY_RX_free.notification ! 1;
        :: else;
        fi;
    od;
}

active proctype VIRT_RX() priority 1 {
    unsigned stored : 2 = 2;
    do
    :: stored > 0 -> goto work_RX_active;
    :: CPY_RX_free.notification ? 1 ->

        work_RX_active: ;
        bit notify_copy = 0;
        do
        :: stored > 0 ->
            INSERT(CPY_RX_active, stored);
            notify_copy = 1;
        :: else -> break;
        od

        if
        :: notify_copy && CPY_RX_active.flag && !(CPY_RX_active.notification ?? [1]) ->
            CPY_RX_active.flag = 0;
            CPY_RX_active.notification ! 1;
        :: else;
        fi

        work_RX_free: ;
        do
        :: !EMPTY(CPY_RX_free) ->
            REMOVE(CPY_RX_free, stored);
        :: else -> break;
        od

        CPY_RX_free.flag = 1;

        if
        :: !EMPTY(CPY_RX_free) ->
            CPY_RX_free.flag = 0;
            goto work_RX_free;
        :: else;
        fi
    od;
}
