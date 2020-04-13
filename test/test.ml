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
  | `Error (info, Lexer.Error s) -> false
  | `Error (info, Parser.Error) -> false
  | `Error (info, err) -> false

let _ = 
  Sys.chdir Filename.parent_dir_name;
  Sys.chdir Filename.parent_dir_name;
  Sys.chdir Filename.parent_dir_name

let get_files path =
  Core__.Core_sys.ls_dir path
  |> Base__.List.filter ~f:(fun name -> 
      Core_kernel.Filename.check_suffix name ".p4")

let good_files = Filename.concat "examples" 
    (Filename.concat "checker_tests" "good") |> get_files
let bad_files = Filename.concat "examples" 
    (Filename.concat "checker_tests" "bad") |> get_files

let good_test f file () =
  Alcotest.(check bool) "good test" true 
    (f ["examples"] (Filename.concat "examples" 
                       (Filename.concat "checker_tests" 
                          (Filename.concat "good" file))))

let bad_test f file () =
  Alcotest.(check bool) "bad test" false 
    (f ["examples"] (Filename.concat "examples" 
                       (Filename.concat "checker_tests" 
                          (Filename.concat "bad" file))))

let () =
  let open Alcotest in
  run "Tests" [
    "parser tests good", 
    (Stdlib.List.map (fun name -> 
         test_case name `Quick (good_test parser_test name)) good_files );
    "typecheck tests bad", (Stdlib.List.map (fun name -> 
        test_case name `Quick (bad_test typecheck_test name)) bad_files );
  ] 
