{
open Printf
open Lexing

module C = Command

let is_among words =
  Hashtbl.mem (
  let table = Hashtbl.create 97 in
  List.iter (fun word -> Hashtbl.add table word ()) words;
  table
 )

let definition_keywords =
  ["Axiome"; "Parameter"; "Definition"; "Theorem";
   "Lemma"; "Remark"; "Fixpoint"; "Function"; "Notation";
   "Inductive"; "Record"]

let program_str = "Program"

let other_keywords = ["do"; "forall"; "Prop"; "Type"; "Set";
                      "Next"; "Obligation"; "Qed"; "Program" ]

    (* Keyword recognition. *)

let is_definition_keyword = is_among definition_keywords

let is_other_keyword = is_among other_keywords

let is_keyword =
  is_among (definition_keywords @ other_keywords)

let nbr_spaces_to_remove = ref 0
let is_inductive = ref false
let constructors = Queue.create ()

let conclude_def () =
  Queue.iter
    (fun constr -> 
      C.defineIdent (!C.prefix constr) constr;
      C.indexSee constr !C.current_ident)
    constructors;
  Queue.clear constructors;
  C.conclude_def ()

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

let coq_token_aux = ([^' ' '\t' '\n' '.' '(' '|' ';' '{' '}' ':'] +)
let coq_token =
  '(' (* to be used where comments are properly delt with *)
| '|'
| ';'
| '{'
| '}'
| ":="
| ':'
| ".." '.'?
| coq_token_aux ('.' ('(' [^'*'])?  coq_token_aux)* 


let dot = '.' [' ' '\t' '\n']

let ident =
  ['a'-'z' 'A'-'Z' '_']+ ['a'-'z' 'A'-'Z' '_' '0'-'9' ''']*

let tex_ident = ['a'-'z' 'A'-'Z']+

let number =
  ['0'-'9']+

let label =
  ['a'-'z' 'A'-'Z' '_'  '-' ':' '0'-'9']+

let start_definition =
  ("Program" ' '+)? ("Axiome"| "Parameter"| "Definition"
  | "Theorem"| "Lemma"| "Remark"| "Fixpoint"
  | "Function" | "Instance" | "Inductive")

let open_command = "(*c2l* "

let dot_return = '.' spaces_opt '\n'
let dot_eof = '.' spaces_opt eof

let body = _ * '.' (' ' | '\t' | '\n')

(* Regular mode. Read and translate code. *)

rule main = parse
| empty_line {main lexbuf}
| open_command {treat_command lexbuf}
| spaces_opt "(*" {elim_comment 1 main lexbuf}
| eof {()}
| spaces_opt "Module" spaces ident spaces_opt ":=" 
    {elim_phrase lexbuf}
| spaces_opt "Module" spaces "Type" spaces (ident as tok) 
    { C.enter_module tok;
      elim_phrase lexbuf}

| spaces_opt "Module" spaces (ident as tok) 
    { C.enter_module tok;
      elim_phrase lexbuf}

| spaces_opt "Section" spaces (ident as tok) spaces_opt dot_return
    { C.enter_section tok;
      main lexbuf}
| spaces_opt "End" spaces_opt (coq_token as tok) spaces_opt (dot_return | dot_eof)
    { C.exit_module tok;
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

and keep_comment cont = parse
| "*)"
    { C.normal "*)";
      cont lexbuf}
| "(*"
    { failwith "Kept comments can't be nested"}
| ([^ '*' '('] *) as content
    { C.normal content;
      keep_comment cont lexbuf}
| ('"' [^ '"']* '"') as content
    { (* '"' this comment is here only to come back to proper syntax coloration*)
      C.normal content;
      keep_comment cont lexbuf }
| '*' { C.normal "*";
        keep_comment cont lexbuf}
| '(' { C.normal "(";
        keep_comment cont lexbuf}

and treat_command = parse
| "short:" space* (ident as id) space* "*)"
    { C.set_short_name (C.SNSome id);
      main lexbuf}
| "short" space* "*)"
    { C.set_short_name C.SNShort;
      main lexbuf}
| "super short:" space* (tex_ident as id) space* "*)"
    { C.set_super_short_name (C.SNSome id);
      main lexbuf}
| "super short" space* "*)"
    { C.set_super_short_name C.SNShort;
      main lexbuf}

and treat_def = parse
| (start_definition as start) (spaces as sp) (ident as id)
    { C.set_current_ident id;
      C.keyword start;
      C.spaces (count_spaces sp);
      C.defined id;
      if start = "Inductive" then is_inductive := true;
      treat_content_def lexbuf}
| "Record" (spaces as sp) (ident as id)
    { C.set_current_ident id;
      C.keyword "Record";
      C.spaces (count_spaces sp);
      C.defined id;
      treat_record_end_of_line false lexbuf}
| ""
    { elim_phrase lexbuf }

and treat_record_end_of_line seen_def = parse
| '{'
    { C.normal "{";
      if seen_def then
        treat_record_start_of_line lexbuf
      else 
        treat_record_end_of_line false lexbuf}
| '}' spaces_opt dot
    { C.normal "}.";
      assert seen_def;
      conclude_def ();
      main lexbuf
    }
| ';'
    { C.normal ";";
      assert seen_def;
      treat_record_start_of_line lexbuf}
| coq_token as tok
    { C.normal tok;
      treat_record_end_of_line (if tok = ":=" then true else seen_def) lexbuf}
| (spaces_opt '\n')+ (spaces_opt as sp)
    { C.new_line ();
      C.spaces (max 0 (count_spaces sp - !nbr_spaces_to_remove));
      treat_record_end_of_line seen_def lexbuf}
| spaces as sp
    { C.spaces (count_spaces sp);
      treat_record_end_of_line seen_def lexbuf}
| "(**" ('r'?)
    { C.normal "(*";
      keep_comment (treat_record_end_of_line seen_def) lexbuf}
| "(*"
    {elim_comment 1 (treat_record_end_of_line seen_def) lexbuf}

and treat_record_start_of_line = parse
| (spaces_opt '\n')+ (spaces_opt as sp)
    { C.new_line ();
      C.spaces (max 0 (count_spaces sp - !nbr_spaces_to_remove));
      treat_record_start_of_line lexbuf}
| (spaces_opt as sp) (ident as tok)
    { C.spaces (count_spaces sp);
      C.normal tok;
      Queue.push tok constructors;
      treat_record_end_of_line true lexbuf}
| (spaces_opt as sp) '}' spaces_opt dot
    { C.spaces (count_spaces sp);
      C.normal "}.";
      conclude_def ();
      main lexbuf
    }
| (spaces_opt as sp) "(**" ('r'?)
    { C.spaces (count_spaces sp);
      C.normal "(*";
      keep_comment treat_record_start_of_line lexbuf}
| spaces_opt "(*"
    {elim_comment 1 treat_record_start_of_line lexbuf}
      
and treat_content_def = parse
| '|' (spaces_opt as sp) (ident as tok)
    { C.normal "|";
      C.spaces (count_spaces sp);
      C.normal tok;
      if !is_inductive then
        Queue.push tok constructors;
      treat_content_def lexbuf}
| '|' (spaces_opt as sp) ((ident ('.' ident)+) as tok)
    { C.normal "|";
      C.spaces (count_spaces sp);
      C.normal tok;
      treat_content_def lexbuf}
| coq_token as tok
    { C.normal tok;
      treat_content_def lexbuf}
| (spaces_opt '\n')+ (spaces_opt as sp)
    { C.new_line ();
      C.spaces (max 0 (count_spaces sp - !nbr_spaces_to_remove));
      treat_content_def lexbuf}
| spaces as sp
    { C.spaces (count_spaces sp);
      treat_content_def lexbuf}
| dot
    { C.normal ".";
      conclude_def ();
      main lexbuf}
| '.' eof
    { C.normal ".";
      conclude_def ()}
| "(**" ('r'?)
    { C.normal "(*";
      keep_comment treat_content_def lexbuf}
| "(*"
    {elim_comment 1 treat_content_def lexbuf}

and elim_phrase =  parse
| coq_token
    { elim_phrase lexbuf}
| spaces_opt '\n' spaces_opt
    { elim_phrase lexbuf}
| spaces
    { elim_phrase lexbuf}
| "..."
    { main lexbuf}
| dot
    { main lexbuf}
| '.' eof
    { () }
| "(*"
    {elim_comment 1 elim_phrase lexbuf}


{

let list_of_file_in_dir dir_name =
  Array.to_list (Sys.readdir dir_name)

let is_coq_file name = 
  Filename.check_suffix name ".v"

let coq_files_in_dir dir_name =
  List.filter is_coq_file (list_of_file_in_dir dir_name)

let dirs = Queue.create ()
let files = Queue.create ()

let () = 
  Arg.parse
    [("-o", Arg.String (fun out -> Command.out_channel := 
                          open_out_gen [Open_text; Open_append] 666 out),
      "The output file (append at the end)");
     ("-O", Arg.String (fun out -> Command.out_channel := open_out out),
      "The output file (overwrite it)")]
    (fun anon ->
      if is_coq_file anon then
        Queue.add anon files
      else
        Queue.add anon dirs)
    "A coq to tex parser. List the files and/or directories to explore";
  Queue.iter (fun dir ->
    let dir_name = if dir = "." then "" else dir in
    let coq_files = coq_files_in_dir dir in
    List.iter (fun file_name ->
      Command.set_directory_and_file_name dir_name file_name;
      let in_chan = open_in (Filename.concat dir_name file_name) in
      Command.modules_list := [];
      main (from_channel in_chan);
      close_in in_chan) coq_files
    ) dirs;
  Queue.iter (fun file ->
    let dir_name = Filename.dirname file in
    let file_name = Filename.basename file in
    Command.set_directory_and_file_name dir_name file_name;
    let in_chan = open_in (Filename.concat dir_name file_name) in
    Command.modules_list := [];
    main (from_channel in_chan);
    close_in in_chan) files
}
