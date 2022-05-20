[ 1 2 ] open-input
u8 1 assert-eq

# open another bitstring
[ 3 ] open-input
offset 0 assert-eq
remain 8 assert-eq
u8 3 assert-eq
input [ 3 ] >bitstr assert-eq
close-input

# check that everyting is same as before
offset 8 assert-eq
remain 8 assert-eq
u8 2 assert-eq
remain 0 assert-eq
close-input

offset 0 assert-eq
remain 0 assert-eq
