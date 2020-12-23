320 var FIRE_WIDTH
168 var FIRE_HEIGHT

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
] var PALETTE

FIRE_WIDTH FIRE_HEIGHT minifb_new var fb

[
FIRE_HEIGHT dec FIRE_WIDTH * 0 do 0 loop
FIRE_WIDTH 0 do 36 loop
] var fire_img

: fire_img_update
    # this trick eliminate fire_img copy
    fire_img
    nil -> fire_img
    assoc -> fire_img
;

: fire_img_get
    fire_img get
;

: calc_offset
    FIRE_WIDTH - random 3 * round -
;

: calc_color
    fire_img_get random 3 * round 1 band -
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
            FIRE_WIDTH I * J + spread_fire
        loop
    loop
;

: draw_fire_pixel
    I J rot fb minifb_put_pixel
;    

: draw_fire
    FIRE_WIDTH 0 do
        FIRE_HEIGHT 0 do
            FIRE_WIDTH I * J + fire_img_get
            PALETTE get
            0xff000000 bor  # add alpha
            draw_fire_pixel
        loop
    loop
;

begin fb minifb_is_open while
    update_fire
    draw_fire
    fb minifb_update
repeat
