
#define QUEUE_SIZE 5

chan notification = [1] of {bit};
unsigned global_tail : 3 = 0;
unsigned global_head : 3 = 0;
bool start = true;

active proctype Producer() {
    unsigned last_tail : 3 = 0;
    bool crossed = false;
    do
        :: (global_tail - global_head) != QUEUE_SIZE ->
            bool inserted = false;
            
            do
                :: (global_tail - global_head) != QUEUE_SIZE ->
                    global_tail = global_tail + 1;
                    if 
                        :: global_head == last_tail -> crossed = true;
                        ::else;
                    fi
                    inserted = true;
                :: (global_head != global_tail) -> break;
            od

            if 
                :: (inserted && (global_head - last_tail >= 0 || crossed)) || start ->
                    crossed = false;
                    notification ! 1;
                    start = false;
                :: else;
            fi

            last_tail = global_tail;
    od;
}

active proctype Consumer() {
    do
        :: notification ? 1 ->
        Consumer_start: ;
            do
                :: global_head != global_tail ->
                    global_head = global_head + 1;
                :: else -> break;
            od

            if 
                :: global_head != global_tail ->
                    goto Consumer_start;
                :: else;
            fi
    od;
}