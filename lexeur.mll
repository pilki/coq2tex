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

let is_keyword =
  is_among (definition_keywords @ other_keywords)
