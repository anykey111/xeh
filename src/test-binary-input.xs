
[ 3 ] bitstr-open
bitstr-input [ 3 ] >bitstr assert-eq
[ 1 2 ] bitstr-open
bitstr-input-deck [ [ ] >bitstr [ 3 ] >bitstr ] assert-eq
u8 1 assert-eq
u8 2 assert-eq
remain 0 assert-eq
bitstr-close
remain 8 assert-eq
bitstr-input [ 3 ] >bitstr assert-eq
u8 3 assert-eq
remain 0 assert-eq
