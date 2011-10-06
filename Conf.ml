(* configuration module *)
open Printf
(*module type PRINTER = sig
  val myprintf : ('a, out_channel, unit) format -> 'a
  val myprint_string: string -> unit
end

module Config(P:PRINTER) = struct
open P*)

let prefix = "\\CTT"
let pref s = prefix ^ s

let b_keyword buf s = bprintf buf "%s" s
let b_defined buf s = bprintf buf "%s"s
let b_normal buf s = bprintf buf "%s"s
let b_newline buf = bprintf buf "%s""\n"
let b_spaces buf n = bprintf buf "%s" (String.make ' ' n)
let b_indexDef buf def = bprintf buf "\\indexDef{%s}\n" def
let b_indexSee buf def see= bprintf buf "\\indexSee{%s}{%s}\n" def see

let p_def out_chan long_name ident main_def extra_def short_name super_short_name =
  fprintf out_chan
"\\begin{SaveVerbatim}{%s}
%s
\\end{SaveVerbatim}
\CTTDefineDef{%s}{%s}{%%
%s}\n" long_name main_def long_name ident extra_def;
  (match short_name with
  | None -> ()
  | Some sn ->
      fprintf out_chan "\\CTTDefineIdent{%s}{%s}\n" sn ident);
  (match super_short_name with
  | None -> ()
  | Some sn ->
      fprintf out_chan "\\CTTDefineSuperShortIdent{%s}{%s}\n" sn ident)
      

let directory_sep = '/'
let file_sep = ':'
let module_sep = '!'
