// COMPONENTS: Client, copy, virt tx
// OUTCOME: Deadlock freedom in 54.3 seconds

#define QUEUE_CAPACITY 2

typedef queue {
    chan notification = [1] of {bit};
    bit flag;
    unsigned head : 2;
    unsigned tail : 2;
}

queue RX_free;
queue RX_active;
queue TX_free;
queue TX_active;

#define CURR_EMPTY(l)   (l == 0)
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
    RX_free.tail = 2;
    TX_free.tail = 2;

    TX_active.flag = 1;
    RX_active.flag = 1;
}

active proctype CLIENT() priority 1 {
    unsigned stored : 2;
    bit notify_rx;
    bit notify_tx;
    do
    :: skip ->
        if
        :: TX_free.notification ? 1 ->
            process_tx: ;

            do
            :: !CURR_EMPTY(stored) && !EMPTY(TX_free) ->
                TRANSFER(TX_free, TX_active);
                INSERT(RX_free, stored);
                notify_rx = 1;
                notify_tx = 1;
            :: else -> break;
            od

            if
            :: CURR_EMPTY(stored) || !EMPTY(TX_free) ->
                TX_free.flag = 0;
            :: else ->
                TX_free.flag = 1;
            fi

            if
            :: !CURR_EMPTY(stored) && !EMPTY(TX_free) ->
                TX_free.flag = 0;
                goto process_tx;
            :: else;
            fi

            goto process_rx;

        :: RX_active.notification ? 1 ->
            process_rx: ;

            do
            :: !EMPTY(RX_active) ->
                if
                :: !EMPTY(TX_free) ->
                    TRANSFER(TX_free, TX_active);
                    TRANSFER(RX_active, RX_free);
                    notify_rx = 1;
                    notify_tx = 1;
                :: else ->
                    TX_free.flag = 1;
                    REMOVE(RX_active, stored);
                fi
            :: else -> break;
            od

            RX_active.flag = 1;

            if
            :: !EMPTY(RX_active) ->
                RX_active.flag = 0;
                goto process_rx;
            :: else;
            fi
        fi;

        if
        :: notify_rx && RX_free.flag && !(RX_free.notification ?? [1]) ->
            notify_rx = 0;
            RX_free.flag = 0;
            RX_free.notification ! 1;
        :: else;
        fi;

        if
        :: notify_tx && TX_active.flag && !(TX_active.notification ?? [1]) ->
            notify_tx = 0;
            TX_active.flag = 0;
            TX_active.notification ! 1;
        :: else;
        fi;
    od;
}

active proctype COPY() priority 1 {
    unsigned drv_active : 2 = 0;
    unsigned drv_free : 2 = 2;
    do
    :: drv_free > 0 ->
        drv_active++;
        drv_free--;
    :: drv_active && !EMPTY(RX_free) ->
        goto work_copy;
    :: RX_free.notification ? 1 ->
        work_copy: ;
        bit notify_client = 0;
        do
        :: drv_active > 0 && !EMPTY(RX_free) ->
            TRANSFER(RX_free, RX_active);
            drv_active--;
            drv_free++;
            notify_client = 1;
        :: else -> break;
        od;

        if
        :: drv_active > 0 ->
            RX_free.flag = 1;
        :: else ->
            RX_free.flag = 0;
        fi;

        if
        :: notify_client && RX_active.flag && !(RX_active.notification ?? [1]) ->
            RX_active.flag = 0;
            RX_active.notification ! 1;
        :: else;
        fi;
    od;
}

active proctype VIRT_TX() priority 1 {
    unsigned stored : 2 = 0;
    do
    :: stored > 0 -> goto work_TX_free;
    :: TX_active.notification ? 1 ->

    work_TX_free: ;
    bit notify_client = 0;
    do
    :: stored > 0 ->
        INSERT(TX_free, stored);
        notify_client = 1;
    :: else -> break;
    od;

    if
    :: notify_client && TX_free.flag && !(TX_free.notification ?? [1]) ->
        TX_free.flag = 0;
        TX_free.notification ! 1;
    :: else;
    fi

    work_TX_active: ;
    do
    :: !EMPTY(TX_active) ->
        REMOVE(TX_active, stored);
    :: else -> break;
    od;

    TX_active.flag = 1;

    if
    :: !EMPTY(TX_active) ->
        TX_active.flag = 0;
        goto work_TX_active;
    :: else;
    fi;
    od;
}
