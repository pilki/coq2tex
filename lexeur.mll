{
open Printf
open Lexing

let is_among words =
  Hashtbl.mem (
  let table = Hashtbl.create 97 in
  List.iter (fun word -> Hashtbl.add table word ()) words;
  table
 )

let definition_keywords =
  ["Axiome"; "Parameter"; "Definition"; "Theorem"; "Lemma"; "Remark"; "Fixpoint"; "Function"; "Notation";]

let program_str = "Program"

let other_keywords = ["do"; "forall"; "Prop"; "Type"; "Set"; "Next"; "Obligation"; "Qed"; "Program" ]

    (* Keyword recognition. *)

let is_definition_keyword = is_among definition_keywords

let is_other_keyword = is_among other_keywords

let is_keyword =
  is_among (definition_keywords @ other_keywords)

let nbr_spaces_to_remove = ref 0

let count_spaces s =
  let c = ref 0 in
  String.iter (function
    | ' ' -> incr c
    | '\t' -> c := !c + 8
    | _ -> failwith "Only spaces should be used for spaces") s;
  !c

}

let space =
  [' ' '\t']

let spaces = space+

let spaces_opt = space*

let empty_line = space* '\n'

let coq_token =
  ([^' ' '\t' '\n' '.' '('] +)
| '(' (* to be used where comments are properly delt with *)
| (['a'-'z' 'A'-'Z' '_' '0' - '9']+ '.' ['a'-'z' 'A'-'Z' '_' '0'-'9']+) (* something with a dot in it *)

let dot = '.' [' ' '\t' '\n']

let ident =
  ['a'-'z' 'A'-'Z' '_']+ ['a'-'z' 'A'-'Z' '_' '0'-'9']*

let tex_ident = ['a'-'z' 'A'-'Z']+

let number =
  ['0'-'9']+

let label =
  ['a'-'z' 'A'-'Z' '_'  '-' ':' '0'-'9']+

let start_definition =
  ("Program" ' '+)? ("Axiome"| "Parameter"| "Definition"| "Theorem"| "Lemma"| "Remark"| "Fixpoint"| "Function" | "Instance")

let open_command = "(*c2l* "

let body = _ * '.' (' ' | '\t' | '\n')

(* Regular mode. Read and translate code. *)

rule elim_lines = parse
| empty_line {elim_lines lexbuf}
| open_command {treat_command lexbuf}
| "(*" {elim_comment 1 elim_lines lexbuf}
| eof {()}
| spaces_opt as sps
    { nbr_spaces_to_remove := count_spaces sps;
      treat_def lexbuf}

and elim_comment n cont = parse
| "*)"
    { if n = 1 then cont lexbuf else elim_comment (pred n) cont lexbuf}
| "(*"
    { elim_comment (succ n) cont lexbuf}
| [^ '*' '('] *
    { elim_comment n cont lexbuf}
| '"' [^ '"']* '"'
    { (* '"' this comment is here only to come back to proper syntax coloration*)
      elim_comment n cont lexbuf }
| '*' { elim_comment n cont lexbuf}
| '(' { elim_comment n cont lexbuf}

and treat_command = parse
| "short:" (tex_ident (*as id*)) space* "*)"
    { elim_lines lexbuf}

and treat_def = parse
| (start_definition as start) (spaces as sp) (ident as id)
    { Printf.printf "*%s*%s|%s|" start sp id;
      treat_content_def lexbuf}
| ""
    { elim_phrase lexbuf }

and treat_content_def = parse
| coq_token as tok
    { Printf.printf "/%s/" tok;
      treat_content_def lexbuf}
| spaces_opt '\n' (spaces_opt as sp)
    { Command.newline ();
      Command.spaces (max 0 (count_spaces sp - !nbr_spaces_to_remove));
      treat_content_def lexbuf}
| dot
    { Printf.printf ".\n";
      elim_lines lexbuf}
| '.' eof
    { Printf.printf ".\n" }
| "(*"
    {elim_comment 1 treat_content_def lexbuf}

and elim_phrase =  parse
| coq_token
    { treat_content_def lexbuf}
| spaces_opt '\n' spaces_opt
    { treat_content_def lexbuf}
| dot
    { elim_lines lexbuf}
| '.' eof
    { () }
| "(*"
    {elim_comment 1 elim_phrase lexbuf}


{
  let () =
    elim_lines (from_channel (open_in (Sys.argv.(1))))
}
