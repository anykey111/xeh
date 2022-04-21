[ 1 2 ] open-bitstr
u8 1 assert-eq

# open another bitstring
[ 3 ] open-bitstr
offset 0 assert-eq
remain 8 assert-eq
u8 3 assert-eq
current-bitstr [ 3 ] >bitstr assert-eq
close-bitstr

# check that everyting is same as before
offset 8 assert-eq
remain 8 assert-eq
u8 2 assert-eq
remain 0 assert-eq
close-bitstr

offset 0 assert-eq
remain 0 assert-eq
