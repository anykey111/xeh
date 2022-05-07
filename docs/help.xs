

: doc-for-stack!  # "Stack Manipulation" 
    doc ;
: doc-for-cond!  # "Conditional Execution"  
    doc ;
: doc-for-tags!  # "Tags" 
    doc ;


"( val tag -- val )
Stick tag to the val. If value already has a tag drop the old one."
"with-tag" doc-for-tags!

"( val -- tag )
Read tag of the value or nil if tag is absent."
"tag-of" doc-for-tags!

"( vec val -- vec )
Append new value to the vec or replace if
val with the same tag already exists."
"insert-tagged" doc-for-tags!


"Conditional branch.

    FLAG if CODE endif

If FLAG is non-zero CODE is executed."
"if" doc-for-cond!


"Fallback for *if* conditional branch.

    FLAG if CODE1 else CODE2 endif
    
If FLAG is zero then CODE2 is executed."
"else" doc-for-cond!


"End of the conditional branch.

    FLAG if CODE endif

If FLAG is zero then CODE is not executed."
"endif" doc-for-cond!


"Select one case of the multiple different choices.

    X case
        X1 of CODE1 endof
        XN of CODEN endof
        DEFAULT
    endcase

Compare X with X1, if X equals to X1 then CODE1 is executed.
Compare X with XN, if X equals to XN then CODEN is executed.
Otherwise DEFAULT is executed."

dup "case" doc-for-cond!
dup "endcase" doc-for-cond!
dup "of" doc-for-cond!
"endof" doc-for-cond!


"Loop with pre-condition.

    begin FLAG while CODE repeat

If FLAG is true CODE is executed and loop is restarted from *begin*.
IF FLAG is false execution continue after the *repeat*.
The FLAG is tested on every loop iteration."
dup "begin" doc
dup "while" doc
"repeat" doc


"Endless loop.

    begin CODE again

Repat CODE forever, unless *exit* or *leave* is called."
"again" doc


"Loop with post-condition.

    begin CODE FLAG until

Restart loop until FLAG evaluates to false."
"until" doc


"Leave the innermost loop immediatly."
"leave" doc


"Loop for every integer starting from START and up to, but excluding LIMIT.
    
    LIMIT START do CODE loop

The current loop index can be accessed with I.
J is used to access the outer loop index and the outermost loop index is K.

    10 0 do I println loop

    5 var num-rows
    10 var num-columns
    num-rows 0 do
        num-columns do
            \"row=\" print J print
            \"col=\" print I println
        loop
    loop
"
dup "do" doc
dup "loop" doc
dup "I" doc
dup "J" doc
 "K" doc

