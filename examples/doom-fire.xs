320 const FIRE_WIDTH
168 const FIRE_HEIGHT

[
    0x070707
    0x1F0707
    0x2F0F07
    0x470F07
    0x571707
    0x671F07
    0x771F07
    0x8F2707
    0x9F2F07
    0xAF3F07
    0xBF4707
    0xC74707
    0xDF4F07
    0xDF5707
    0xDF5707
    0xD75F07
    0xD75F07
    0xD7670F
    0xCF6F0F
    0xCF770F
    0xCF7F0F
    0xCF8717
    0xC78717
    0xC78F17
    0xC7971F
    0xBF9F1F
    0xBF9F1F
    0xBFA727
    0xBFA727
    0xBFAF2F
    0xB7AF2F
    0xB7B72F
    0xB7B737
    0xCFCF6F
    0xDFDF9F
    0xEFEFC7
    0xFFFFFF
] const PALETTE

var fb
FIRE_WIDTH FIRE_HEIGHT minifb_new -> fb

var fire_img
FIRE_WIDTH FIRE_HEIGHT * bytearray_new -> fire_img
FIRE_WIDTH 0 do
    36
    FIRE_HEIGHT 1- FIRE_WIDTH * i +
    fire_img bytearray_set
loop

: fire_img_update
    fire_img bytearray_set
;

: fire_img_get
    fire_img bytearray_get
;

: calc_offset
    FIRE_WIDTH - random 3 * round -
;

: calc_color
    fire_img_get random 3 * round 1 bit-and -
;

: spread_fire_random
    dup calc_color
    swap calc_offset
    fire_img_update
;

: spread_fire
    dup fire_img_get if
        spread_fire_random
    else
        FIRE_WIDTH -
        0 swap 
        fire_img_update
    then
;

: update_fire
    FIRE_WIDTH 0 do
        FIRE_HEIGHT 2 do
            FIRE_WIDTH i * j + spread_fire
        loop
    loop
;

: draw_fire_pixel
    i j rot fb minifb_put_pixel
;    

: draw_fire
    FIRE_WIDTH 0 do
        FIRE_HEIGHT 0 do
            FIRE_WIDTH i * j + fire_img_get
            PALETTE get
            0xff000000 bit-or  # add alpha
            draw_fire_pixel
        loop
    loop
;

begin fb minifb_is_open while
    update_fire
    draw_fire
    fb minifb_update
repeat
