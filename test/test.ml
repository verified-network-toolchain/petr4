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
  Printf.printf "Testing file %s...\n" p4_file;
  match Parse.parse_file include_dirs p4_file false with
  | `Ok prog ->
    begin
      try
        let prog, renamer = Elaborate.elab prog in
        let _ = Checker.check_program renamer prog in
        true
      with
      | Error.Type(info, err) ->
        Format.eprintf "%s: %a" (Info.to_string info) Error.format_error err;
        false
      | exn ->
        Format.eprintf "Unknown exception: %s" (Exn.to_string exn);
        false
    end
  | `Error (info, Lexer.Error s) -> false
  | `Error (info, Parser.Error) -> false
  | `Error (info, err) -> false

let get_files path =
  Sys.ls_dir path
  |> List.filter ~f:(fun name ->
      Core_kernel.Filename.check_suffix name ".p4")

let example_path l =
  let root = Filename.concat ".." "examples" in
  List.fold_left l ~init:root ~f:Filename.concat

let good_files = example_path ["checker_tests"; "good"] |> get_files
let excluded_good_files = example_path ["checker_tests"; "excluded/good"] |> get_files

let bad_files = example_path ["checker_tests"; "bad"] |> get_files
let excluded_bad_files = example_path ["checker_tests"; "excluded/bad"] |> get_files

(* This is a hack, sorry! *)
let known_failures =
  ["default-control-argument.p4";
   "cast-call.p4";
   "issue1803_same_table_name.p4";
   "issue1541.p4";
   "issue1672-bmv2.p4";
   "issue1932.p4";
   "table-entries-optional-2-bmv2.p4";
   "control-verify.p4";
   "div1.p4";
   "table-entries-lpm-2.p4";
   "default-control-argument.p4"]

let good_test f file () =
  Alcotest.(check bool) "good test" true
    (f ["../examples"] (example_path ["checker_tests"; "good"; file]))

let bad_test f file () =
  Alcotest.(check bool) "bad test" false
    (f ["../examples"] (example_path ["checker_tests"; "bad"; file]))

let excl_test file () =
  Alcotest.(check bool) "good test" true true

let () =
  let open Alcotest in
  run "Tests" [
    "excluded tests good", (Stdlib.List.map (fun name ->
        test_case name `Quick (excl_test name)) excluded_good_files);
    "excluded tests bad", (Stdlib.List.map (fun name ->
        test_case name `Quick (excl_test name)) excluded_bad_files);
    "parser tests good", (Stdlib.List.map (fun name ->
        test_case name `Quick (good_test parser_test name)) (good_files@bad_files));
    "typecheck tests good", (Stdlib.List.map (fun name ->
        let speed = if List.mem ~equal:String.equal known_failures name then `Slow else `Quick in
        test_case name speed (good_test typecheck_test name)) good_files);
    "typecheck tests bad", (Stdlib.List.map (fun name ->
        let speed = if List.mem ~equal:String.equal known_failures name then `Slow else `Quick in
        test_case name speed (bad_test typecheck_test name)) bad_files);
  ]
