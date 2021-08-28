big-endian

[ "NES" 0x1a ] ?
u8 var prg-len
u8 var chr-len
u8 var flags6
u8 var flags7
u8 var ram-banks
1 uint var PAL
7 uint var reserved1
5 bytes var reserved2
flags6 0b100 band if
  512 bytes var trainer-data
then
offset var prg-offset
prg-len 16384 * bytes var prg-data
offset var chr-offset
chr-len 8192 * bytes var chr-data

(8 8 *) var tile-len

: nes-tile-read
  [ tile-len for 1 uint loop ] local plane1
  [ tile-len for 1 uint loop ] local plane2
  [
    tile-len for
      plane1 I nth
      plane2 I nth 1 bshl
      bor
    loop
  ]
;

: nes-tile-draw
  8 * local screen-y
  8 * local screen-x
  local tile
  tile-len for
    # set palette index
    tile I nth d2-color!
    # x
    screen-x I 8 rem +
    # y
    screen-y I 8 / +
    d2-data!
  loop
;

: nes-chr-draw
  256 256 d2-resize
  [ 0xffE0E0E0 0xffC0C0C0 0xffA0A0A0 0xff808080 ] d2-palette!
  remain (16 8 *) / local ntiles
  ntiles for
    nes-tile-read
    I 16 rem
    I 16 /
    nes-tile-draw
  loop
;

chr-offset seek
nes-chr-draw

snapshot
restore
