big-endian

[
    256 0 do
        24 unsigned 0xff00_0000 bit-or
    loop
] const pal

: zoom 32 * ;

var fb
16 zoom 16 zoom minifb_new -> fb

: draw_color
    local color
    zoom local y
    zoom local x
    1 zoom 0 do
        1 zoom 0 do
            x i +
            y j +
            color
            fb
            minifb_put_pixel
        loop
    loop
;

16 0 do
    16 0 do
        i
        j
        j 16 * i + pal get
        draw_color
    loop
loop

begin fb minifb_is_open while
    fb minifb_update
repeat