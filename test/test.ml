open Core
open Petr4
open Common

module Conf: Parse_config = struct
  let red s = s
  let green s = s

  let preprocess include_dirs p4file =
    let cmd =
      String.concat ~sep:" "
        (["cc"] @
         (List.map include_dirs ~f:(Printf.sprintf "-I%s") @
          ["-undef"; "-nostdinc"; "-E"; "-x"; "c"; p4file])) in
    let in_chan = Unix.open_process_in cmd in
    let str = In_channel.input_all in_chan in
    let _ = Unix.close_process_in in_chan in
    str
end

module Parse = Make_parse(Conf)

let parser_test include_dirs file = 
  match Parse.parse_file include_dirs file false with 
  | `Ok _ -> true
  | `Error _ -> false

let typecheck_test (include_dirs : string list) (p4_file : string) : bool =
  match Parse.parse_file include_dirs p4_file false with
  | `Ok prog ->
    let prog = Elaborate.elab prog in
    Checker.check_program prog |> ignore; true
  | `Error (info, Lexer.Error s) ->
    (*Format.eprintf "%s: %s@\n%!" (Info.to_string info) s;*) false
  | `Error (info, Parser.Error) ->
    (*Format.eprintf "%s: syntax error@\n%!" (Info.to_string info);*) false
  | `Error (info, err) ->
    (*Format.eprintf "%s: %s@\n%!" (Info.to_string info) (Exn.to_string err);*) false

let _ = 
  Sys.chdir Filename.parent_dir_name;
  Sys.chdir Filename.parent_dir_name;
  Sys.chdir Filename.parent_dir_name; 
  Sys.chdir "test"

let path file = Filename.concat "examples" file

let file_lst = Core__.Core_sys.ls_dir "examples"

let test f file () =
  Alcotest.(check bool) "returns true" true (f ["examples"] (path file))

let () =
  let open Alcotest in
  run "Tests" [
    "parser tests", 
    (Stdlib.List.map (fun name -> 
         test_case name `Quick (test parser_test name)) file_lst );
    "typecheck tests", (Stdlib.List.map (fun name -> 
        test_case name `Quick (test typecheck_test name)) file_lst );
  ] 
