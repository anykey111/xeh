(
"Conditional branch.

    FLAG if CODE endif

If FLAG is non-zero CODE is executed.
"
"if" doc
)

(
"Fallback for *if* conditional branch.

    FLAG if CODE1 else CODE2 endif
    
If FLAG is zero then CODE2 is executed.
"
"else" doc
)

(
"End of the conditional branch.

    FLAG if CODE endif

If FLAG is zero then CODE is not executed.
"

"endif" doc
)

(
"
    X case
        X1 of CODE1 endof
        X2 of CODE2 endof
        DEFAULT
    endcase

Compare X with X1, X2 and so on.
If X equals to X1 then CODE1 is executed.
If X equals to X2 then CODE2 is executed.
Otherwise DEFAULT is executed.
DEFAULT is not mandatory and migth be empty.
"
dup "case" doc
dup "endcase" doc
dup "of" doc
"endof" doc
)

(
"Simple conditional loop.

    begin FLAG while CODE repeat

If FLAG is true CODE is executed and loop is restarted from *begin*.
IF FLAG is false execution continue after the *repeat*.
THe FLAG is tested on every loop iteration.
"
dup "begin" doc
dup "while" doc
"repeat" doc
)

(
"Simple endless loop.

    begin CODE again

Repat CODE forever, unless *exit* or *leave* called.
"
"again" doc
)

(
"Simple conditional loop.

    begin CODE FLAG until

Restart loop until FLAG evaluates to false.
"
"until" doc
)

(
"Stop loop execution.
It is an error to use *leave* outside of the loop.
"
"leave" doc
)
