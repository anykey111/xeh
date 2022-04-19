
[ 3 ] open-bitstr
bitstr-input [ 3 ] >bitstr assert-eq
[ 1 2 ] open-bitstr
binary-stash [ [ ] >bitstr [ 3 ] >bitstr ] assert-eq
u8 1 assert-eq
u8 2 assert-eq
remain 0 assert-eq
close-bitstr
remain 8 assert-eq
bitstr-input [ 3 ] >bitstr assert-eq
u8 3 assert-eq
remain 0 assert-eq
