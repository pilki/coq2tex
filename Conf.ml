(* configuration module *)

let prefix = "\\c2l"
let pref s = prefix ^ s

let keyword_cmd = pref "keyword"
let defined_cmd = pref "defined"
let other_cmd = pref "other"

let space_cmd = pref "space"
let newline_cmd = "\\\\"

let directory_sep = '/'
let module_sep = ':'
let extra_sep = '!'

let indexDef = "\\indexDef"
let indexSec = "\\indexSec"

