open Sig
open Printf

let out_channel = ref stdout

let directory_name = ref "XXXXXXXXX DN NOT SET YET XXXXXXXXXXX"
let file_name = ref "XXXXXXXXX FN NOT SET YET XXXXXXXXXXX"
let prefix_string = ref "XXXXXXXXX PS NOT SET YET XXXXXXXXXXX"

  (* prefix of the form directory/Foo *)
let set_directory_and_file_name dn fn =
  directory_name := dn;
  file_name := fn;
  prefix_string := sprintf "%s%c%s%c" !directory_name Conf.directory_sep !file_name Conf.module_sep

let modules_list = ref []

  (* prefix mod_lst name returns directory/Foo:Mod1:Mod2:name *)
let prefix_aux () =
  let long_prefix =
    List.fold_left
      (fun prefix mod_name -> sprintf "%s%c%s" prefix Conf.module_sep mod_name)
      !prefix_string (List.rev !modules_list) in
  fun name ->
    long_prefix ^ name

let prefix = ref (prefix_aux ())

let enter_module module_name =
  modules_list := module_name :: !modules_list;
  prefix := prefix_aux ()

let exit_module module_name =
  match !modules_list with
  | [] -> failwith (sprintf "Exit a module (%s), but no module !" module_name)
  | hd :: tl ->
      if hd <> module_name then
        failwith (sprintf "Exit the module %s but was in module %s" module_name hd);
      modules_list := tl;
      prefix := prefix_aux ()


let myoutput s = output_string !out_channel s
let myprintf (*: 'a. ('a, out_channel, unit) format -> 'a *)=
  fun f -> fprintf !out_channel f


let spaces n =
  for i = 1 to n do
    myoutput Conf.space_cmd
  done

let newline () =
  myoutput Conf.newline_cmd

let keyword s =
  myprintf "%s{%s}" Conf.keyword_cmd s

let defined s =
  myprintf "%s{%s}" Conf.defined_cmd s

let other s =
  myprintf "%s{%s}" Conf.other_cmd s

let indexDef s = myprintf "%s{%s}" Conf.indexDef s
let indexSec s = myprintf "%s{%s}" Conf.indexSec s

let def_short_name short long =
  myprintf "Def of short '%s': %s\n" short long

let def_super_short_name short long =
  myprintf "Def of super short '%s': %s\n" short long

