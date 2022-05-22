# Quick reference

## Comments

```
    # single line comment
    # must be separated with whitespace
    #this-is-not-a-comment
```

## Literals

```
    # decimal
    7 -99 1_000
    
    # hex
    0xff 0x11_EE
    
    # binary
    0b11111 0b1111_1111
    
    # real 
    2.78 -1.2e-5
    
    # string
    "escapes \\ \" \r \n \t"          

    # boolean flag
    true false
    
    # vector
    [ 1 2 3.0 "abc" ]

    # no value
    nil

    # bit-string consist of arbitrary number of bits
    # hex digits 0..9 A..F represent 4 bit chunk of data
    # "-" and "x" represent a single bit
    |F1|    # 0b1111_0001
    |x--x|  # 0b1001
    |F1x|   # 0b1111_0001_1
```

## Words and variables

1. Word name consist of any symbols, but can't start with digit or double quite.
2. Words are separated by whitespaces
3. Variable is a special word that holds reference to the value

```
    # valid words
    +[]
    _"d^%$$$#112d'"d+"
    a0000-/-)(22)
    .99

    # invalid words
    0waa
    9sss
    "abc

    # define global variable 
    0 var counter
    # set a new value 
    10 ! counter

    # define a new word
    : increment-counter
        counter 1 + ! counter
    ;

    # locals
    : shuffle3
        local c
        local b 
        local a
        b a c ;
    1 2 3 shuffle-3
```

## Meta evaluation and constants

```
    # Code inside the round brackets evaluated at build time
    ( 1 2 + )
    
    # define a constant
    ( 1.0 60.0 / ) var FRAME-TIME

    # also have the read-only access to the global environment
    : fib dup 1 > if
            dup 2 - fib
            swap 1 - fib
            +
        endif ;
    ( 20 fib ) var fib-of-20
```

## Conditional execution

```
    true if "yes" else "no" endif println

    # select one case of the multiple different choices
    false case
        true of 1 endof
        false of 0 endof
    endcase

    # case with fallback
    3 case
        0 of "a" endof
        1 of "b" endof
        # fallback, drop unmatched value 2 from the stack
        drop "c"
    endcase
```

## Basic loops

```
    # loop with pre-codnition, test condition before every iteration
    begin remain 5 > while
        read-more
    repeat

    # post condition, restart loop if condition is false
    begin read-byte zero? until

    # endless loop
    begin
        day-of-week "friday" = if
            # leave is used to break loop execution
            leave
        endif 
    repeat
```
    
## Counter loops

```
    # count from 0 to 10, current loop index is accessed with "I"
    10 0 do I print loop

    # outer loop index is accessed with J
    10 5 do # J
        5 0 do # I
            "J=" print J print
            "I=" print I print
        loop
        newline
    loop
```

## Tags

Tag is a special data sticked to the value but not directly accessed.

```
    # stick "abc" string to the integer 10
    10 "abc" with-tag
    var X
    # tag have no impact on using value
    X 5 + println 
    # get tag of X
    X tag-of println
    
    # shorthand syntax for literal tags
    10 . "ten"
    10 "ten" with-tag

    # stick vector
    "text" .[ 14 . "size" "red" . "color" ]
    "text" [ 14 "size" with-tag "red" "color" with-tag ] with-tag
```

