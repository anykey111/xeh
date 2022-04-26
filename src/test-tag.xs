
10 "ten!" with-tag

dup 10 assert-eq

dup tag-of "ten!" assert-eq

"a" "b" "c" with-tag with-tag

dup tag-of "b" assert-eq

dup tag-of tag-of "c" assert-eq

22 33 , tag-of 33 assert-eq
