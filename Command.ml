open Sig
open Printf

let out_channel = ref stdout
let directory_name = ref "XXXXXXXXX DN NOT SET YET XXXXXXXXXXX"
let file_name = ref "XXXXXXXXX FN NOT SET YET XXXXXXXXXXX"
let prefix_string = ref "XXXXXXXXX PS NOT SET YET XXXXXXXXXXX"


(* list of entered modules, in reverse order *)
let modules_list = ref []

(* prefix mod_lst name returns directory/Foo.v:Mod1!Mod2!name *)
let prefix_aux () =
  let long_prefix =
    List.fold_left
      (fun prefix (mod_name, is_module) -> 
        if is_module then sprintf "%s%c%s" prefix Conf.module_sep mod_name else prefix)
      !prefix_string (List.rev !modules_list) in
  fun name ->
    long_prefix ^ name

(* !prefix id produces the long ident form of id *)
let prefix = ref (prefix_aux ())

(* prefix of the form directory/Foo *)
let set_directory_and_file_name dn fn =
  directory_name := dn;
  file_name := fn;
  prefix_string :=
    if dn = "" then 
      sprintf "%s%c" !file_name Conf.file_sep
    else
      sprintf "%s%c%s%c"
        !directory_name Conf.directory_sep
        !file_name Conf.file_sep;
  prefix := prefix_aux ()

let enter_module module_name =
  modules_list := (module_name, true) :: !modules_list;
  prefix := prefix_aux ()

let enter_section module_name =
  modules_list := (module_name, false) :: !modules_list

let exit_module module_name =
  match !modules_list with
  | [] ->
      failwith (sprintf "Exit a module (%s), but no module was open!" module_name)
  | (mn, _) :: tl ->
      if mn <> module_name then
        failwith (sprintf "Exit the module %s but was in module %s" module_name mn);
      modules_list := tl;
      prefix := prefix_aux ()

(* the different buffers *)

let main_def_buffer = Buffer.create 2048
let extra_def_buffer = Buffer.create 2048


let spaces n = 
  Conf.b_spaces main_def_buffer n
let new_line () =
  Conf.b_newline main_def_buffer
let keyword s =
  Conf.b_keyword main_def_buffer s
let normal s =
  Conf.b_normal main_def_buffer s
let defined s =
  Conf.b_defined main_def_buffer s
let indexSee def see =
  Conf.b_indexSee extra_def_buffer def see


type short_name =
  | SNNone
  | SNShort
  | SNSome of string

let current_ident = ref ""
let short_name = ref SNNone
let super_short_name = ref SNNone


let set_short_name sn = short_name := sn
let set_super_short_name ssn = super_short_name := ssn
let set_current_ident ident = current_ident := ident
let get_current_ident () = !current_ident

let short_to_id = function
  | SNNone -> None
  | SNShort -> Some !current_ident
  | SNSome s -> Some s

let conclude_def () =
  Conf.p_def !out_channel (!prefix !current_ident) !current_ident
    (Buffer.contents main_def_buffer) (Buffer.contents extra_def_buffer)
    (short_to_id !short_name) (short_to_id !super_short_name);
  (* clean up every mutable state *)
  current_ident := "";
  short_name := SNNone;
  super_short_name := SNNone;
  Buffer.clear main_def_buffer;
  Buffer.clear extra_def_buffer
