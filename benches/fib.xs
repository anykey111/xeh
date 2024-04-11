
: fib
    dup 1 > if
        dup 2 - fib
        swap 1 - fib
        +
    then
;

# 15 0 do     i fib "," print print loop
35 fib println
