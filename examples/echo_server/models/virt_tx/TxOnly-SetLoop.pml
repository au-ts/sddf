// COMPONENTS: Client0, virt tx, eth
// OUTCOME: Deadlock freedom:
// - One client verifies in 7.08 seconds

#define QUEUE_CAPACITY 2
#define CLIENT_NUM 1

typedef queue {
    chan notification = [1] of {bit};
    bit flag;
    unsigned head : 2;
    unsigned tail : 2;
}
queue CLT0_TX_free;
queue CLT0_TX_active;

queue ETH_TX_free;
queue ETH_TX_active;

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
    CLT0_TX_free.flag = 1;
    CLT0_TX_active.flag = 1;

    ETH_TX_active.flag = 1;
    ETH_TX_free.flag = 1;
}

active proctype CLIENT0() priority 1 {
    bit notify_tx = 0;
    do
    :: skip ->
        if
        :: !EMPTY(CLT0_TX_free) ->
            goto work_clt_start;

        :: CLT0_TX_free.notification ? 1 ->
            work_clt_start: ;

            unsigned to_send : 2 = 1;
            do
            :: to_send < QUEUE_CAPACITY ->
                to_send++;
            :: skip ->
                break;
            od;

            work_clt: ;

            do
            :: !EMPTY(CLT0_TX_free) && to_send > 0 ->
                TRANSFER(CLT0_TX_free, CLT0_TX_active);
                to_send--;
                notify_tx = 1;
            :: else -> break;
            od

            if
            :: EMPTY(CLT0_TX_free) && to_send > 0 ->
                CLT0_TX_free.flag = 1;
            :: else ->
                CLT0_TX_free.flag = 0;
            fi

            if
            :: !EMPTY(CLT0_TX_free) && to_send > 0 ->
                CLT0_TX_free.flag = 0;
                goto work_clt;
            :: else;
            fi;
        fi;

        if
        :: notify_tx && CLT0_TX_active.flag && !(CLT0_TX_active.notification ?? [1]) ->
            notify_tx = 0;
            CLT0_TX_active.flag = 0;
            CLT0_TX_active.notification ! 1;
        :: else;
        fi;
    od;
}

active proctype VIRT_TX() priority 1 {
    do
    :: ETH_TX_free.notification ? 1 -> goto work_virt_tx_start;
    :: CLT0_TX_active.notification ? 1 ->

        work_virt_tx_start: ;
        bit notify_eth = 0;
        bit notify_client[CLIENT_NUM] = {0};

        work_virt_tx_free: ;
        do
        :: !EMPTY(ETH_TX_free) ->
            TRANSFER(ETH_TX_free, CLT0_TX_free);
            notify_client[0] = 1;
        :: else -> break;
        od

        ETH_TX_free.flag = 1;

        if
        :: !EMPTY(ETH_TX_free) ->
            ETH_TX_free.flag = 0;
            goto work_virt_tx_free;
        :: else;
        fi;

        if
        :: notify_client[0] && CLT0_TX_free.flag && !(CLT0_TX_free.notification ?? [1]) ->
            CLT0_TX_free.flag = 0;
            CLT0_TX_free.notification ! 1;
        :: else;
        fi

        work_virt_tx_active_0: ;
        do
        :: !EMPTY(CLT0_TX_active) ->
            TRANSFER(CLT0_TX_active, ETH_TX_active);
            notify_eth = 1;
        :: else -> break;
        od;

        CLT0_TX_active.flag = 1;

        if
        :: !EMPTY(CLT0_TX_active) ->
            CLT0_TX_active.flag = 0;
            goto work_virt_tx_active_0;
        :: else;
        fi;

        if
        :: notify_eth && ETH_TX_active.flag && !(ETH_TX_active.notification ?? [1]) ->
            ETH_TX_active.flag = 0;
            ETH_TX_active.notification ! 1;
        :: else;
        fi
    od;
}

active proctype ETH() priority 1 {
    unsigned dev_active : 3 = 2;
    unsigned dev_free : 2 = 0;
    do
    :: dev_active > 0 ->
        dev_active--;
        dev_free++;
    :: ETH_TX_active.notification ? 1 ->
        work_eth_tx: ;
        do
        :: !EMPTY(ETH_TX_active)->
            REMOVE(ETH_TX_active, dev_active);
        :: else -> break
        od

        ETH_TX_active.flag = 1;

        if
        :: !EMPTY(ETH_TX_active) ->
            ETH_TX_active.flag = 0;
            goto work_eth_tx;
        :: else;
        fi;

    :: dev_free > 0 ->
        bit notify_tx = 0;

        do
        :: dev_free > 0 ->
            INSERT(ETH_TX_free, dev_free);
            notify_tx = 1;
        :: else -> break;
        od

        if
        :: notify_tx && ETH_TX_free.flag && !(ETH_TX_free.notification ?? [1])->
            ETH_TX_free.flag = 0;
            ETH_TX_free.notification ! 1;
        :: else;
        fi
    od
}
