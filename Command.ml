open Sig
open Printf

module Cmd (Out:OUTCHAN) = struct


  (* prefix of the form directory/Foo *)
  let prefix_string = sprintf "%s%c%s%c" Out.directory_name Conf.directory_sep Out.file_name Conf.module_sep


  (* prefix mod_lst name returns directory/Foo:Mod1:Mod2:name *)
  let prefix mod_lst =
    let long_prefix =
      List.fold_left
        (fun pref mod_name -> sprintf "%s%c%s" pref Conf.module_sep mod_name)
        prefix_string mod_lst in
    fun name ->
      long_prefix ^ name


  let myoutput s = output_string Out.out s
  let myprintf = fprintf out


  let space n =
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


end
