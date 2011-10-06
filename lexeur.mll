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
  ["Axiome"; "Parameter"; "Definition"; "Theorem"; "Lemma"; "Remark"; "Fixpoint"; "Function"; "Notation"; "Inductive"; "Record"]

let program_str = "Program"

let other_keywords = ["do"; "forall"; "Prop"; "Type"; "Set"; "Next"; "Obligation"; "Qed"; "Program" ]

    (* Keyword recognition. *)

let is_definition_keyword = is_among definition_keywords

let is_other_keyword = is_among other_keywords

let is_keyword =
  is_among (definition_keywords @ other_keywords)

type short_name =
  | SNNone
  | SNShort
  | SNSome of string

let nbr_spaces_to_remove = ref 0
let current_def = ref ""
let short_name = ref SNNone
let super_short_name = ref None
let is_inductive = ref false
let constructors = Queue.create ()

let conclude_def () =
  (match !short_name with
  | SNNone -> ()
  | SNShort -> 
      Command.def_short_name !current_def !current_def
  | SNSome sn ->
      Command.def_short_name sn !current_def);
  (match !super_short_name with
  | None -> ()
  | Some ssn ->
      Command.def_super_short_name ssn !current_def);
  Queue.iter (fun constr -> Command.myprintf "Constructor %s (see %s)\n"
                 constr !current_def) constructors;
  short_name := SNNone;
  super_short_name := None;
  is_inductive := false;
  Queue.clear constructors

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
  ([^' ' '\t' '\n' '.' '(' '|'] +)
| '(' (* to be used where comments are properly delt with *)
| '|'
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
  ("Program" ' '+)? ("Axiome"| "Parameter"| "Definition"| "Theorem"| "Lemma"| "Remark"| "Fixpoint"| "Function" | "Instance" | "Inductive" | "Record")

let open_command = "(*c2l* "

let body = _ * '.' (' ' | '\t' | '\n')

(* Regular mode. Read and translate code. *)

rule main = parse
| empty_line {main lexbuf}
| open_command {treat_command lexbuf}
| "(*" {elim_comment 1 main lexbuf}
| eof {()}
| spaces_opt "Module" [^'\n']* ":=" [^'\n']* ".\n"
    {main lexbuf}
| spaces_opt "Module" (coq_token as tok) [^'\n' '.']* ".\n"
    { Command.enter_module tok;
      main lexbuf}
| spaces_opt "Section" (coq_token as tok) spaces_opt ".\n"
    { Command.enter_section tok;
      main lexbuf}
| spaces_opt "End" (coq_token as tok) spaces_opt ".\n"
    { Command.exit_module tok;
      main lexbuf}
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
| "short:" space* (ident as id) space* "*)"
    { short_name := SNSome id;
      main lexbuf}
| "short" space* "*)"
    { short_name := SNShort;
      main lexbuf}
| "super short:" space* (tex_ident as id) space* "*)"
    { super_short_name := Some id;
      main lexbuf}

and treat_def = parse
| (start_definition as start) (spaces as sp) (ident as id)
    { Printf.printf "*%s*%s|%s|" start sp id;
      current_def := id;
      if start = "Inductive" then is_inductive := true;
      treat_content_def lexbuf}
| ""
    { elim_phrase lexbuf }

and treat_content_def = parse
| '|' (spaces_opt as sp) (ident as tok)
    { Printf.printf "|";
      Command.spaces (count_spaces sp);
      Command.myprintf "/%s/" tok;
      if !is_inductive then
        Queue.push tok constructors;
      treat_content_def lexbuf}
| coq_token as tok
    { Printf.printf "/%s/" tok;
      treat_content_def lexbuf}
| spaces_opt '\n' (spaces_opt as sp)
    { Command.newline ();
      Command.spaces (max 0 (count_spaces sp - !nbr_spaces_to_remove));
      treat_content_def lexbuf}
| spaces as sp
    { Command.spaces (count_spaces sp);
      treat_content_def lexbuf}
| dot
    { Printf.printf ".\n";
      conclude_def ();
      main lexbuf}
| '.' eof
    { Printf.printf ".\n";
      conclude_def ()}
| "(*"
    {elim_comment 1 treat_content_def lexbuf}

and elim_phrase =  parse
| coq_token 
    { elim_phrase lexbuf}
| spaces_opt '\n' spaces_opt
    { elim_phrase lexbuf}
| spaces
    { elim_phrase lexbuf}
| dot
    { main lexbuf}
| '.' eof
    { () }
| "(*"
    {elim_comment 1 elim_phrase lexbuf}


{
  let () =
    main (from_channel (open_in (Sys.argv.(1))))
}
