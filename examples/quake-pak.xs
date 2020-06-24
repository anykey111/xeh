

: pak-header
    {
        "id" "PACK" ?
        "offset" u32
        "size" u32
        "entries" pak-entry
    }
;

: pak-entry
    {
        "name" 56 bytes
        "offset" u32
        "size" u32
    }
;

