# The HEX Programming Language

XEH is a dynamic, stack-oriented programming language designed for the interactive coding. Main language domain is binary data parsing.
Its look like FORTH, but its not. XEH doesn't provide low-level memory access, uses immutable data structures and reference-counted garbage collector.

Features:

* Builtin debugger with reverse step option.
* Whole program state snapshot and rollback.
* Immutable REPL, evaluate result without commiting changes to the program state until you like it.
* Simple meta-programming, everyting might be evaluated at compile time if it doesn't try to modify runtime state.
* Data tagging, stick attribute to any value, even integer maybe tagged.

Try online:
[XEH Playground](https://anykey111.github.io/)
Chat: [Discord](https://discord.gg/8veCURFW)
Video: [Youtube](https://www.youtube.com/channel/UCYTeJIi6aLE9rS7s_QOto3w)

# Building and Running

```
    # build core library and command line tools
    cargo build --release

    # command line options
    xeh [options] [sources]
    Options:
        -i path             input binary file
        -e expression       evaluate expression
        -r                  enable reverse debugging
        -h, --help          print help

    # repl commands
    /trial          switch to live coding mode
    /repl           switch to REPL mode
    /snapshot       snapshot program state
    /rollback       rollback to the latest snapshot
    /next           debugger - step forward
    /rnext          debugger - step backward
```

# Quick Language Reference

## Comments

```
    # single line comment
    # whitespace or end of line should follow after sharp char
    #this is not a comment
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

## Words, Variables and Locals

By the analogy to the mainstream programming languages, "word" is just a function.

1. Word name consist of any symbols, but can't start with digit or double quote.
2. Words are separated by whitespaces.

```
    # valid words
    abc
    my-name
    +[]
    _"d^%$$$#112d'"d+"
    a0000-/-)(22)
    .99

    # invalid words
    0waa
    9sss
    "abc
```

New word definition starts with ":" then word name and body follow, definition ends with ";".

```
    # define a new word
    : hello "Hello!" println ; 
    # invoke
    hello
```

Variable is just a word that return a single value from the memory cell.
Variable definition starts with "var" word then name follow, initial value is taken from the stack.

```
    # define a new global variable 
    0 var counter
    # set a new value 
    10 ! counter

    # define a new word that increment counter value
    : increment-counter
        counter 1 + ! counter
    ;
```

Local variable is a variable that available only inside the word definition, initial variable is taken from the stack.

```
    # locals
    : print2
        local b 
        local a
        "a = " print a println
        "b = " print b println
    ;
    1 2 print2

```

## Meta evaluation

Code inside the round brackets evaluated at the build time, values left on the stack are passed to the parent context, everything else is wiped (expect constants).

```
    # calculate fib during build time
    : fib dup 1 > if
            dup 2 - fib
            swap 1 - fib
            +
        endif ;
    ( 20 fib ) var fib-of-20
```

## Constants

Constant is a read-only variable that inline its value immediately without
refering to the memory cell.
Initial value is taken from the stack. Constant definition allowed only
from the meta context, because variables yet not evaluated. 

```
    ( 1.0 60.0 / const FRAME-TIME )
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
    
## Counted loops

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
