// COMPONENTS: Copy0, copy1, virt rx, eth
// OUTCOME: Deadlock freedom:
// - One client verifies in 84.2 seconds
// - Impossible to verify two clients simultaneously in exhaustive mode

#define QUEUE_CAPACITY 2
#define CLIENT_NUM 1

typedef queue {
    chan notification = [1] of {bit};
    bit flag;
    unsigned head : 2;
    unsigned tail : 2;
}

queue CPY0_RX_free;
queue CPY0_RX_active;

// queue CPY1_RX_free;
// queue CPY1_RX_active;

queue ETH_RX_free;
queue ETH_RX_active;

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
    CPY0_RX_free.flag = 1;
    CPY0_RX_active.flag = 1;

    // CPY1_RX_free.flag = 1;
    // CPY1_RX_active.flag = 1;

    ETH_RX_active.flag = 1;
    ETH_RX_free.flag = 1;
}

active proctype COPY0() priority 1 {
    do
    :: CPY0_RX_active.notification ? 1 ->
        bit notify_rx = 0;
        work_copy: ;
        do
        :: !EMPTY(CPY0_RX_active) ->
            TRANSFER(CPY0_RX_active, CPY0_RX_free);
            notify_rx = 1;
        :: else -> break;
        od;

        CPY0_RX_active.flag = 1;

        if 
        :: !EMPTY(CPY0_RX_active) ->
            CPY0_RX_active.flag = 0;
            goto work_copy;
        :: else;
        fi

        if 
        :: CPY0_RX_free.flag && notify_rx && !(CPY0_RX_free.notification ?? [1]) -> 
            CPY0_RX_free.flag = 0;
            CPY0_RX_free.notification ! 1;
        :: else;
        fi;
    od;
}

// active proctype COPY1() priority 1 {
//     do
//     :: CPY1_RX_active.notification ? 1 ->
//         bit notify_rx = 0;
//         work_copy: ;
//         do
//         :: !EMPTY(CPY1_RX_active) ->
//             TRANSFER(CPY1_RX_active, CPY1_RX_free);
//             notify_rx = 1;
//         :: else -> break;
//         od;

//         CPY1_RX_active.flag = 1;

//         if 
//         :: !EMPTY(CPY1_RX_active) ->
//             CPY1_RX_active.flag = 0;
//             goto work_copy;
//         :: else;
//         fi

//         if 
//         :: CPY1_RX_free.flag && notify_rx && !(CPY0_RX_free.notification ?? [1]) -> 
//             CPY1_RX_free.flag = 0;
//             // Share one channel but different flags
//             CPY0_RX_free.notification ! 1;
//         :: else;
//         fi;
//     od;
// }

active proctype VIRT_RX() priority 1 {
    do
    :: ETH_RX_active.notification ? 1 -> goto work_virt_rx_start;
    :: CPY0_RX_free.notification ? 1 ->

        work_virt_rx_start: ;
        bit notify_client[CLIENT_NUM] = {0};
        bit notify_eth = 0;

        work_virt_rx_active: ;
        do
        :: !EMPTY(ETH_RX_active) ->
            if
            :: skip ->
                TRANSFER(ETH_RX_active, CPY0_RX_active);
                notify_client[0] = 1;
            // :: skip ->
            //     TRANSFER(ETH_RX_active, CPY1_RX_active);
            //     notify_client[1] = 1;
            :: skip ->
                TRANSFER(ETH_RX_active, ETH_RX_free);
                notify_eth = 1;
            fi;
        :: else -> break;
        od

        ETH_RX_active.flag = 1;

        if
        :: !EMPTY(ETH_RX_active) ->
            ETH_RX_active.flag = 0;
            goto work_virt_rx_active;
        :: else;
        fi

        if
        :: notify_client[0] && CPY0_RX_active.flag && !(CPY0_RX_active.notification ?? [1]) -> 
            CPY0_RX_active.flag = 0;
            CPY0_RX_active.notification ! 1;
        :: else;
        fi

        // if
        // :: notify_client[1] && CPY1_RX_active.flag && !(CPY1_RX_active.notification ?? [1]) -> 
        //     CPY1_RX_active.flag = 0;
        //     CPY1_RX_active.notification ! 1;
        // :: else;
        // fi

        work_virt_rx_free_0: ;
        do
        :: !EMPTY(CPY0_RX_free) ->
            TRANSFER(CPY0_RX_free, ETH_RX_free);
            notify_eth = 1;
        :: else -> break;
        od

        CPY0_RX_free.flag = 1;

        if
        :: !EMPTY(CPY0_RX_free) -> 
            CPY0_RX_free.flag = 0;
            goto work_virt_rx_free_0;
        :: else;
        fi

        // work_virt_rx_free_1: ;
        // do
        // :: !EMPTY(CPY1_RX_free) ->
        //     TRANSFER(CPY1_RX_free, ETH_RX_free);
        //     notify_eth = 1;
        // :: else -> break;
        // od

        // CPY1_RX_free.flag = 1;

        // if
        // :: !EMPTY(CPY1_RX_free) -> 
        //     CPY1_RX_free.flag = 0;
        //     goto work_virt_rx_free_1;
        // :: else;
        // fi

        if
        :: notify_eth && ETH_RX_free.flag && !(ETH_RX_free.notification ?? [1]) -> 
            ETH_RX_free.flag = 0;
            ETH_RX_free.notification ! 1;
        :: else;
        fi
    od;
}

active proctype ETH() priority 1 {
    unsigned dev_active : 2 = 0;
    unsigned dev_free : 2 = 2;
    do
    :: dev_free > 0 ->
        dev_active++;
        dev_free--;

    :: ETH_RX_free.notification ? 1 ->
        work_eth_rx: ;
        do
        :: !EMPTY(ETH_RX_free) ->
            REMOVE(ETH_RX_free, dev_free);
        :: else -> break
        od

        if
        :: dev_free + dev_active < QUEUE_CAPACITY ->
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

    :: dev_active > 0 ->
        bit notify_rx = 0;

        do
        :: dev_active > 0 ->
            INSERT(ETH_RX_active, dev_active);
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
