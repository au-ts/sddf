// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

// COMPONENTS: Virt tx, virt rx, eth driver, device
// OUTCOME: Deadlock freedom:
// - RX path verifies in 0.24 seconds
// - TX path verifies in 0.15 seconds
// - Impossible to verify both paths simultaneously in exhaustive mode

#define QUEUE_CAPACITY 2

typedef queue {
    chan notification = [1] of {bit};
    bit flag;
    unsigned head : 2;
    unsigned tail : 2;
}

queue ETH_RX_free;
queue ETH_RX_active;
queue ETH_TX_free;
queue ETH_TX_active;

typedef dev_queue {
    unsigned head : 2;
    unsigned tail : 2;
    unsigned next : 2;
}

chan IRQ_RX = [1] of {bit};
chan IRQ_TX = [1] of {bit};

dev_queue HW_RX;
dev_queue HW_TX;

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

#define BUFS_PROCESSED(q) (q.next != q.head)
#define BUFS_AVAILABLE(q) (q.next != q.tail)
#define PROCESS_BUF(q) q.next++

init priority 2 {
    HW_RX.tail = 2;
    ETH_RX_free.flag = 1;
    ETH_RX_active.flag = 1;

    HW_TX.tail = 2;
    ETH_TX_free.flag = 1;
    ETH_TX_active.flag = 1;
}

active proctype VIRT_RX() priority 1 {
    unsigned stored : 2 = 0;
    do
    :: stored > 0 -> goto work_virt_rx;
    :: ETH_RX_active.notification ? 1 ->

        work_virt_rx: ;
        bit notify_eth = 0;
        do
        :: !EMPTY(ETH_RX_active) ->
            if
            :: skip ->
                TRANSFER(ETH_RX_active, ETH_RX_free);
                notify_eth = 1;
            :: skip ->
                REMOVE(ETH_RX_active, stored);
            fi
        :: else -> break;
        od

        ETH_RX_active.flag = 1;

        if
        :: !EMPTY(ETH_RX_active) ->
            ETH_RX_active.flag = 0;
            goto work_virt_rx;
        :: else;
        fi;

        do
        :: stored > 0 ->
            INSERT(ETH_RX_free, stored);
            notify_eth = 1;
        :: else -> break;
        od

        if
        :: notify_eth && ETH_RX_free.flag && !(ETH_RX_free.notification ?? [1]) ->
            ETH_RX_free.flag = 0;
            ETH_RX_free.notification ! 1;
        :: else;
        fi
    od;
}

active proctype VIRT_TX() priority 1 {
    unsigned stored : 2 = 0;
    do
    :: stored > 0 -> goto work_virt_tx_start;
    :: ETH_TX_free.notification ? 1->
        work_virt_tx_start: ;
        bit notify_eth = 0;
        work_virt_tx: ;
        do
        :: !EMPTY(ETH_TX_free) ->
            REMOVE(ETH_TX_free, stored);
        :: else -> break;
        od;

        ETH_TX_free.flag = 1;

        if
        :: !EMPTY(ETH_TX_free) ->
            ETH_TX_free.flag = 0;
            goto work_virt_tx;
        :: else;
        fi;

        do
        :: stored > 0 ->
            INSERT(ETH_TX_active, stored);
            notify_eth = 1;
        :: else -> break;
        od;

        if
        :: notify_eth && ETH_TX_active.flag && !(ETH_TX_active.notification ?? [1]) ->
            ETH_TX_active.flag = 0;
            ETH_TX_active.notification ! 1;
        :: else;
        fi
    od;
}

active proctype ETH() priority 1 {
    do
    :: ETH_TX_active.notification ? 1 ->
        work_eth_tx: ;
        do
        :: !EMPTY(ETH_TX_active) ->
            TRANSFER(ETH_TX_active, HW_TX);
        :: else -> break
        od

        ETH_TX_active.flag = 1;

        if
        :: !EMPTY(ETH_TX_active) ->
            ETH_TX_active.flag = 0;
            goto work_eth_tx;
        :: else;
        fi;

    :: ETH_RX_free.notification ? 1 ->
        work_eth_rx: ;

        do
        :: !EMPTY(ETH_RX_free) ->
            TRANSFER(ETH_RX_free, HW_RX);
        :: else -> break
        od

        if
        :: !FULL(HW_RX) ->
            ETH_RX_free.flag = 1;
        :: else ->
            ETH_RX_free.flag = 0;
        fi

        if
        :: !EMPTY(ETH_RX_free) ->
            ETH_RX_free.flag = 0;
            goto work_eth_rx;
        :: else;
        fi;

    :: IRQ_TX ? 1 ->
        bit notify_tx = 0;
        do
        :: !EMPTY(HW_TX) && BUFS_PROCESSED(HW_TX) ->
            TRANSFER(HW_TX, ETH_TX_free);
            notify_tx = 1;
        :: else -> break;
        od

        if
        :: notify_tx && ETH_TX_free.flag && !(ETH_TX_free.notification ?? [1])->
            ETH_TX_free.flag = 0;
            ETH_TX_free.notification ! 1;
        :: else;
        fi

    :: IRQ_RX ? 1 ->
        bit notify_rx = 0;
        do
        :: !EMPTY(HW_RX) && BUFS_PROCESSED(HW_RX) ->
            TRANSFER(HW_RX, ETH_RX_active);
            notify_rx = 1;
        :: else -> break;
        od

        if
        :: notify_rx && ETH_RX_active.flag && !(ETH_RX_active.notification ?? [1]) ->
            ETH_RX_active.flag = 0;
            ETH_RX_active.notification ! 1;
        :: else;
        fi

        goto work_eth_rx;
    od
}

active proctype DEV() priority 1 {
    do
    :: !EMPTY(HW_RX) && BUFS_AVAILABLE(HW_RX) ->
        PROCESS_BUF(HW_RX);

        if
        :: IRQ_RX ?? [1];
        :: else -> IRQ_RX ! 1;
        fi

    :: !EMPTY(HW_TX) && BUFS_AVAILABLE(HW_TX) ->
        PROCESS_BUF(HW_TX);

        if
        :: IRQ_TX ?? [1];
        :: else -> IRQ_TX ! 1;
        fi
    od
}
