
: @comment "comment" with-tag multi-tag ;

: .comment "comment" find-tagged ;

10 "ten!" @comment 

dup 10 assert-eq

dup .comment "ten!" assert-eq

dup "comment" . "ten!" assert-eq

dup tag [ "ten!" ] assert-eq

dup tag 0 get tag "comment" assert-eq
