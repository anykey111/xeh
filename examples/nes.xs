big-endian

[ "NES" 0x1a ] magic-bytes
u8 var prg-len
u8 var chr-len
u8 var flags6
u8 var flags7
u8 var ram-banks
1 uint var PAL
7 uint var reserved1
5 bytes var reserved2

flags6 0b100 band if
  512
else
  0
endif bytes var tainer-data

offset var prg-offset
prg-len 16384 * bytes var prg-data
offset var chr-offset
chr-len 8192 * bytes var chr-data

( 8 8 * ) var tile-len

: nes-tile-read
  [ tile-len 0 do 1 uint loop ] local plane1
  [ tile-len 0 do 1 uint loop ] local plane2
  [
    tile-len 0 do
      plane1 i get
      plane2 i get 1 bshl
      bor
    loop
  ]
;

: nes-tile-draw
  8 * local screen-y
  8 * local screen-x
  local tile
  tile-len 0 do
    # set palette index
    tile i get d2-color!
    # x
    screen-x i 8 rem +
    # y
    screen-y i 8 / +
    d2-data!
  loop
;

: nes-chr-draw
  256 256 d2-resize
  [ 0xffE0E0E0 0xffC0C0C0 0xffA0A0A0 0xff808080 ] d2-palette!
  remain ( 16 8 * ) / local ntiles
  ntiles 0 do
    nes-tile-read
    i 16 rem
    i 16 /
    nes-tile-draw
  loop
;

chr-offset seek
nes-chr-draw
