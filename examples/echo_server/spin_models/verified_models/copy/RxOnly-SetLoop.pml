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

#define ENQUEUE(q)      q.tail++
#define DEQUEUE(q)      q.head++

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
                DEQUEUE(CLT_RX_active);
                ENQUEUE(CLT_RX_free);
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
        :: notify_rx && CLT_RX_free.flag -> 
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
        bit client_enqueued = 0;
        bit virt_enqueued = 0;
        
        bit reprocess = 1;
        do
        :: reprocess ->
            do
            :: !EMPTY(CPY_RX_active) ->
                if
                :: !EMPTY(CLT_RX_free) ->
                    DEQUEUE(CLT_RX_free);
                    DEQUEUE(CPY_RX_active);
                    ENQUEUE(CLT_RX_active);
                    ENQUEUE(CPY_RX_free);
                    client_enqueued = 1;
                :: else ->
                    DEQUEUE(CPY_RX_active);
                    ENQUEUE(CPY_RX_free);
                fi;
                virt_enqueued = 1;
            :: else -> break;
            od;

            CPY_RX_active.flag = 1;

            reprocess = 0;
            if
            :: !EMPTY(CPY_RX_active) ->
                CPY_RX_active.flag = 0;
                reprocess = 1;
            :: else;
            fi;
        :: else -> break;
        od;

        if
        :: client_enqueued && CLT_RX_active.flag ->
            CLT_RX_active.flag = 0;
            CLT_RX_active.notification ! 1;
        :: else;
        fi;

        if
        :: virt_enqueued && CPY_RX_free.flag ->
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
        :: notify_copy && CPY_RX_active.flag -> 
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
