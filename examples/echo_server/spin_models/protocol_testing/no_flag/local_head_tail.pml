
#define QUEUE_SIZE 5

chan notification = [1] of {bit};
unsigned global_tail : 3 = 0;
unsigned global_head : 3 = 0;

active proctype Producer() {
    unsigned last_tail : 3 = 0;
    do
        :: (global_tail - global_head) != QUEUE_SIZE ->
            bool inserted = false;
            unsigned local_tail : 3 = global_tail;
            
            do
                :: (local_tail - global_head) != QUEUE_SIZE ->
                    local_tail = local_tail + 1;
                    inserted = true;
                :: skip -> break;
            od

            global_tail = local_tail;

            if 
                :: inserted && (global_head == last_tail) ->
                    notification ! 1;
                :: else;
            fi

            last_tail = local_tail;
    od;
}

active proctype Consumer() {
    do
        :: notification ? 1 ->
        Consumer_start: ;
            unsigned local_head : 3 = global_head;

            do
                :: local_head != global_tail ->
                    local_head = local_head + 1;
                :: (global_tail - local_head) != QUEUE_SIZE -> break;
            od

            global_head = local_head;

            if 
                :: local_head != global_tail ->
                    goto Consumer_start;
                :: else;
            fi
    od;
}