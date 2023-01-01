# The HEX Programming Language

XEH is a dynamic, stack-oriented programming language designed for the interactive coding. Main language domain is binary data parsing.
Its look like FORTH, but its not. XEH uses immutable data structures and reference-counting garbage collector.

Features:

* Builtin reverse debugger.
* Trial and error REPL mode, preview result of the evaluation without commiting the changes.
* Runtime compilation and compile-time evaluation.
* Tagging, arbitrary annotation of data.

Try online:
[XEH Playground](https://anykey111.github.io/)
Chat: [Discord](https://discord.gg/8veCURFW)
Video: [Youtube](https://www.youtube.com/@xeh-lang)

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
    # hex digits 0-9 and A-F represent 4 bit chunk of data
    # letters "o" and "i" represent a single bit, zero and one
    |F1|    # 0b1111_0001
    |iooi|  # 0b1001
    |F1i|   # 0b1111_0001_1
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
Special word "!" sets the new value of variable.

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

Local variable is a variable that available only inside the word definition, initial value is taken from the stack.
Local variable is read-only.

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

Tag is a special hidden property sticked to the value but not directly accessed.
Tags have no impact on using value and dissapear after value modification.

```
    # stick "abc" string to the integer 10
    10 "abc" with-tag
    var X
    # get tag of X
    X tag-of println
    
    # addition produce new value without any tags
    # in that case tag-of return nil
    2 . "number" 2 + tag-of println

    # shorthand syntax for literal tags
    10 . "ten"
    10 "ten" with-tag

    # stick vector
    "text" .[ 14 . "size" "red" . "color" ]
    "text" [ 14 "size" with-tag "red" "color" with-tag ] with-tag
```

## Meta evaluation and compilation

Source code execution operate in three modes:

    * Compilation - source code translation to the virtual machine bytecode
    * Evaluation - execution of the generated bytecode
    * Meta evaluation - using the result of the source code execution as input for compilation

User is free to switch forth and back between the modes.
When compiler see the round bracket it switch to the meta mode, then execute code till the closing bracket.
All values on the stack are passed to the parent mode.

```
    : fib dup 1 > if
            dup 2 - fib
            swap 1 - fib
            +
        endif
    ;

    # compute Fibonacci number at compile-time
    ( 20 fib ) var fib-of-20
```

## Constants

Constant is a read-only variable that inline its value immediately without
refering to the memory cell.
Initial value is taken from the stack and must be defined inside of the meta mode.

```
    ( 1.0 60.0 / const FRAME-TIME )
```

## Advanced variable definition

Advanced variable definition starts with `let` word,
then pattern description follow, definition ends with `in` word.
Every name in the pattern bind the new variable, literal in the pattern
ensure that value is exactly same, otherwise error is raised.
Word `else` in the pattern define alternative error handling path.

```
    # bind 1 to a
    1 let a in
    # test, a = 1
    a let 1 in 
    # error, a <> 2
    a let 2 in
    # custom error handler
    a let 2 else "invalid value" println in
    # bind multiple values from the vec
    [ [ 1 2 ] [ 3 4 ] ] let [ [ a b ] [ c d ] ] in
    # bind all remaining items
    [ 1 2 3 5 7  ] let [ a b & rest ]
    # bind tag of the value
    \"x\" 10 with-tag let val . tag in
```

## Source code injection

Meta evaluation result might serve as input for compilation.When compiler see immediate word `~)` instead of the closing bracket, first compiler join result into a string and then treat that string as a part of the source code.

```
    # assign number for each name starting from 0
    : my-enum
        local names
        names length 0 do
            [ I " var " names I get ] concat
        loop
    ;
    
    # define variables from list
    ( [ "aa" "bb" "cc" ] my-enum ~)

    bb println 
```
