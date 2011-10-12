(* configuration module *)
open Printf
(*module type PRINTER = sig
  val myprintf : ('a, out_channel, unit) format -> 'a
  val myprint_string: string -> unit
end

module Config(P:PRINTER) = struct
open P*)

let strip__ s =
  let s = String.copy s in
  for i = 0 to String.length s - 1 do
    if s.[i] = '_' then s.[i] <- ' '
  done;
  s



let prefix = "\\CTT"
let pref s = prefix ^ s

let b_keyword buf s = bprintf buf "%s" s
let b_defined buf s = bprintf buf "%s"s
let b_normal buf s = bprintf buf "%s"s
let b_newline buf = bprintf buf "%s""\n"
let b_spaces buf n = bprintf buf "%s" (String.make n ' ')
let b_indexDef buf def = bprintf buf "\\indexDef{%s}\n" def
let b_indexSee buf ident long_name_def long_name_see =
  bprintf buf "\\indexSee{%s@\\CTTIdent*{%s}}{\\CTTIdent*{%s}}\n"
    (strip__ ident) long_name_def long_name_see

let b_defineIdent buf long_name ident =
  bprintf buf "\\SaveVerb{__CTT__IDENT%s}§%s§\n" long_name ident


let p_def out_chan long_name ident main_def extra_def ident_def short_name super_short_name =
  fprintf out_chan
"\\begin{SaveVerbatim}{%s}
%s
\\end{SaveVerbatim}
\\SaveVerb{__CTT__IDENT%s}§%s§
\\CTTDefineDef{%s}{%s}{%%
%s}
%s\n" long_name main_def long_name ident long_name (strip__ ident) extra_def ident_def;
  (match short_name with
  | None -> ()
  | Some sn ->
      fprintf out_chan "\\SaveVerb{__CTT__IDENT%s}§%s§\n" sn ident);
  (match super_short_name with
  | None -> ()
  | Some sn ->
      fprintf out_chan "\\CTTDefineSuperShortIdent{%s}{%s}\n" sn long_name);
  fprintf out_chan "\n"
      

let directory_sep = '/'
let file_sep = ':'
let module_sep = ':'
