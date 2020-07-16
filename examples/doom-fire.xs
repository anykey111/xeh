(320 const FIRE_WIDTH)
(168 const FIRE_HEIGHT)

([
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
] const PALETTE)

var fire_img
[ 
    1 FIRE_HEIGHT - FIRE_WIDTH * 0 do 0 loop
    FIRE_WIDTH 0 do 36 loop
] -> fire_img

: fire_img_update
    fire_img rot assoc -> fire_img
;

: random_offset
    random 3 * round
;

: spread_fire_random
    local index
    random_offset
    dup bitand 1 # mask offset
    index fire_img get - # substract from color
    swap # offset color
    1 + # increase offset by 1
    FIRE_WIDTH index -
    -
    fire_img_update
;

: spread_fire
    dup fire_img get if
        spread_fire_random
    else
        FIRE_WIDTH -
        0 swap
        fire_img_update
    then
;

: update_fire
    FIRE_WIDTH 0 do
        FIRE_HEIGHT 1 do
            FIRE_WIDTH i * j + spread_fire
        loop
    loop
;

var fb
FIRE_WIDTH FIRE_HEIGHT minifb_new -> fb

begin fb minifb_is_open while
    update_fire
    fb minifb_update
repeat
