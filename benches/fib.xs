
: fib
    dup 2 < if
        drop 1
    else
        dup 2 - fib
        swap 1 - fib
        +
    then
;

36 fib .
