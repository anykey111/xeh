
: doc-for-loop "Conditional Loops" "section" with-tag ;
: doc-for-stack "Stack Manipulation" "section" with-tag ;
: doc-for-cond  "Conditional Execution" "section" with-tag ;
: doc-for-tags "Tags" "section" with-tag ;
: doc-for-bitstr "Binary Parsing" with-tag ;
: doc-for-fmt "Formatting" with-tag ;
: doc-for-doc "Documentation" with-tag ;
: stack-comment "stack-comment" with-tag ;
: doc-example "example" with-tag ;

"Add help string for word."
@[ doc-for-doc "str str --" stack-comment
    "\"Help string for \"fun1\" \"fun1\" doc!" doc-example
] "doc!" doc!

"Print help string for word."
@[ doc-for-doc "str --" stack-comment
    "\"fun1\" help" doc-example
] "help" doc!

"Get string for word."
@[ doc-for-doc "str -- str" stack-comment
"\"fun1\" help-str println" doc-example
] "help-str" doc!

"Stick tag to the val. If value already has a tag drop the old one."
@[ doc-for-tags
    "val tag -- val" stack-comment 
] "with-tag" doc!

"Read tag of the value or nil if tag is absent."
@[ doc-for-tags
    "val -- tag" stack-comment
] "tag-of" doc!

"Append new value to the vec or replace if
val with the same tag already exists."
@[ doc-for-tags
    "vec val -- vec" stack-comment
] "insert-tagged" doc!

"Execute code if flag is true, otherwise jump to \"endif\".
    FLAG if CODE endif"
@[ doc-for-cond
] "if" doc!

"Fallback for the \"if\" conditional branch. Executed when flag is false.
    FLAG if CODE else FALLBACK endif"
@[ doc-for-cond
] "else" doc!

"End of the \"if\" conditional branch."
@[ doc-for-cond
] "endif" doc!

"Select one case of the multiple different choices.
    X case
        X1 of CODE1 endof
        XN of CODEN endof
        DEFAULT
    endcase
Compare X with X1, if X equals to X1 then CODE1 is executed.
Compare X with XN, if X equals to XN then CODEN is executed.
Otherwise DEFAULT is executed."
@[ doc-for-cond
] dup "of" doc! "case" doc!

"End of the \"case\" conditional select." 
@[ doc-for-cond
] "endcase" doc!

"End of the single case selection." 
@[ doc-for-cond
] "endof" doc!

"Loop with pre-condition.
    begin FLAG while CODE repeat
If FLAG is true CODE is executed and loop is restarted from \"begin\".
IF FLAG is false execution continue after the \"repeat\".
The FLAG is tested on every loop iteration."
@[ doc-for-loop 
] dup "begin" doc! dup "while" doc! "repeat" doc!

"Endless loop.
    begin CODE again
Repat CODE forever, unless \"exit\" or \"leave\" is called."
@[ doc-for-loop
] "again" doc!

"Loop with post-condition.
    begin CODE FLAG until
Restart loop until flag is false."
@[ doc-for-loop
] "until" doc!

"Leave the innermost loop immediatly."
@[ doc-for-loop
] "leave" doc!

"Loop for every integer starting from START and up to, but excluding LIMIT.
    LIMIT START do CODE loop
The current loop index can be accessed with I.
J is used to access the outer loop index and the outermost loop index is K."
@[ doc-for-loop
"10 0 do \".\" println loop" doc-example
"5 var num-rows
10 var num-columns
num-rows 0 do
    num-columns do
        \"row=\" print J print
        \"col=\" print I println
    loop
loop" doc-example
] dup "do" doc!  "loop" doc!

"Innermost loop index"
@[ doc-for-loop "-- int" stack-comment ] "I" doc!

"Outer loop index"
@[ doc-for-loop "-- int" stack-comment ] "J" doc!

"Outermost loop index"
@[ doc-for-loop "-- int" stack-comment ] "K" doc!

"Binary data under inspection."
@[ doc-for-bitstr 
    "-- bitstr" stack-comment
] "input" doc!

"Number of bits consumed."
@[ doc-for-bitstr
    "-- int" stack-comment
] "offset" doc!

"Number of bits remain unread."
@[ doc-for-bitstr
    "-- int" stack-comment
] "remain" doc!

"Temporary open the new binary until the close-input called."
@[ doc-for-bitstr 
    "bitstr --" stack-comment
] "open-input" doc!

"Drop current binary, restore the previous one from oh-hold."
@[ doc-for-bitstr ] "close-input" doc!

"Reposition offset."
@[ doc-for-bitstr
    "int --" stack-comment
] "seek" doc!

"True if default endianess is set to big."
@[ doc-for-bitstr
    "flag --" stack-comment
] "big?" doc!

"Set big endian as default."
@[ doc-for-bitstr ] "big" doc!

"Set little endian as default."
@[ doc-for-bitstr ] "little" doc!
 
"Find the first occurence or nil starting from the current offset."
@[ doc-for-bitstr
    "bytestr -- int" stack-comment
] "find" doc!

"Print dump from the current offset."
@[ doc-for-bitstr
    "--" stack-comment
] "dump" doc!

"Print dump at the given offset."
@[ doc-for-bitstr
    "int --" stack-comment
] "dump-at" doc!

"Read number of bits as bitstr."
@[ doc-for-bitstr
    "int -- bitstr" stack-comment
] "bitstr" doc!

"Formatting option, set the number base to 16."
@[ doc-for-fmt
"13 HEX println" doc-example
] "HEX" doc!

"Formatting option, set the number base to 2."
@[ doc-for-fmt
"5 BIN println" doc-example
] "BIN" doc!

"Formatting option, set the number base to 10."
@[ doc-for-fmt
"13 HEX print 13 DEC println" doc-example
] "DEC" doc!

"Formatting option, set the number base to 8."
@[ doc-for-fmt
"13 OCT println" doc-example
] "OCT" doc!

"Formatting option, display the number prefix."
@[ doc-for-fmt
] "PREFIX" doc!

"Formatting option, omit the number prefix."
@[ doc-for-fmt
] "NO-PREFIX" doc!

"Formatting option, display the tag sticked to the value."
@[ doc-for-fmt ] "TAGS" doc!

"Formatting option, omit the tag sticked to the value."
@[ doc-for-fmt ] "NO-TAGS" doc!

depth 0 = assert