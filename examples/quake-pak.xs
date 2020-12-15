

: quake-pak-header
    {
        "id" "PACK" ?
        "offset" u32
        "size" u32
    }
;

: quake-pak-entry
    {
        "name" 56 bytes
        "offset" u32
        "size" u32
    }
;

: quake-pak-read-entry
    local entry
    entry "offset" get 8 * binary-input-seek
    entry "size" get bytes
    "data" entry assoc
;

var quake-pak-list

: quake-pak-open
    quake-pak-header local header
    "size" header get 64 / local count
    [ count 0 do quake-pak-entry loop ] local entries
    [ count 0 do i entries get quake-pak-read-entry loop ]
    dup -> quake-pak-list
;

: quake-pak-extract
    quake-pak-list get "data" get
    swap fs/write 
;
