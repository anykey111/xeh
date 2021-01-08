
#0-3      String "NES^Z" used to recognize .NES files.
#4        Number of 16kB ROM banks.
#5        Number of 8kB VROM banks.
#6        bit 0     1 for vertical mirroring, 0 for horizontal mirroring.
#         bit 1     1 for battery-backed RAM at $6000-$7FFF.
#         bit 2     1 for a 512-byte trainer at $7000-$71FF.
#         bit 3     1 for a four-screen VRAM layout. 
#         bit 4-7   Four lower bits of ROM Mapper Type.
#7        bit 0     1 for VS-System cartridges.
#         bit 1-3   Reserved, must be zeroes!
#         bit 4-7   Four higher bits of ROM Mapper Type.
#8        Number of 8kB RAM banks. For compatibility with the previous
#         versions of the .NES format, assume 1x8kB RAM page when this
#         byte is zero.
#9        bit 0     1 for PAL cartridges, otherwise assume NTSC.
#         bit 1-7   Reserved, must be zeroes!
#10-15    Reserved, must be zeroes!
#16-...   ROM banks, in ascending order. If a trainer is present, its
#         512 bytes precede the ROM bank contents.
#...-EOF  VROM banks, in ascending order.

big-endian

"NES" ?
u8 var _1a
u8 var prg-len
u8 var chr-len
u8 var flags6
u8 var flags7
u8 var ram-banks
1 unsigned var PAL
7 unsigned var reserved1
5 bytes var reserved2
flags6 0b100 band if
  512 bytes var trainer-data
then
offset var prg-offset
prg-len 16384 * bytes var prg-data
offset var chr-offset
chr-len 8192 * bytes var chr-data

nil var fb

# Each tile in the pattern table is 16 bytes, made of two planes.
# The first plane controls bit 0 of the color the second plane controls bit 1. Any pixel whose color is 0 is background
# p1  p2  color
# 0 	0 	0
# 1 	0 	1
# 0 	1 	2
# 1 	1 	3 

(8 8 *) var tile-len

: nes-tile-read
  [ tile-len 0 do 1 unsigned loop ] local plane1
  [ tile-len 0 do 1 unsigned loop ] local plane2
  [
    tile-len 0 do
      I plane1 get
      I plane2 get 1 bshl
      bor
    loop
  ]
;

[ 0xffE0E0E0 0xffC0C0C0 0xffA0A0A0 0xff808080 ] var nes-ppu-pal

: nes-ppu-color
  nes-ppu-pal get
;

: nes-tile-draw
  8 * local y
  8 * local x
  local tile
  tile-len 0 do
    # x tile coordinate inverted 
    8 I 8 rem - x +
    I 8 / y +
    I tile get nes-ppu-color
    fb
    minifb_put_pixel  
  loop
;

: nes-chr-draw
  2 -> minifb-default-scale
  256 256 minifb_new -> fb
  remain (16 8 *) / local ntiles
  ntiles 0 do
    nes-tile-read
    I 16 rem
    I 16 /
    nes-tile-draw
  loop
  fb minifb_update
;

chr-offset seek
nes-chr-draw
