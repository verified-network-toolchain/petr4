open Core
open Petr4
let parser_test include_dirs file =
  let cfg = Pass.mk_parse_only include_dirs file in
  match Petr4.Unix.Driver.run_parser cfg with
  | Ok _ -> true
  | Error e ->
    Printf.eprintf "error in parser test: %s" (Petr4.Common.error_to_string e);
    false

let typecheck_test include_dirs file =
  Printf.printf "Testing file %s...\n" file;
  let cfg = Pass.mk_check_only include_dirs file in
  match Petr4.Unix.Driver.run_checker cfg with
  | Ok _ -> true
  | Error e ->
    Printf.eprintf "error in checker test: %s" (Petr4.Common.error_to_string e);
    false

let get_files path =
  Sys_unix.ls_dir path
  |> List.filter
       ~f:(fun name -> Filename.check_suffix name ".p4")

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
   "issue1672-bmv2.p4";
   "table-entries-optional-2-bmv2.p4";
   "control-verify.p4";
   "div1.p4";
   "table-entries-lpm-2.p4";
   "default-control-argument.p4";
   "virtual3.p4";
   "issue2037.p4"]

let good_test f file () =
  Alcotest.(check bool) (Printf.sprintf "good/%s" file) true
    (f ["../examples"] (example_path ["checker_tests"; "good"; file]))

let bad_test f file () =
  Alcotest.(check bool) (Printf.sprintf "bad/%s" file) false
    (f ["../examples"] (example_path ["checker_tests"; "bad"; file]))

let excl_test file () =
  Alcotest.(check bool) (Printf.sprintf "excluded %s" file) true true

let classify_test name =
  if List.mem ~equal:String.equal known_failures name
  then `Slow
  else `Quick

let () =
  let open Alcotest in
  run "Tests" [
    "excl-pos", (Stdlib.List.map (fun name ->
        test_case name `Quick (excl_test name)) excluded_good_files);
    "excl-neg", (Stdlib.List.map (fun name ->
        test_case name `Quick (excl_test name)) excluded_bad_files);
    "parser-pos", (Stdlib.List.map (fun name ->
        test_case name `Quick (good_test parser_test name)) (good_files@bad_files));
    "typing-pos", (Stdlib.List.map (fun name ->
        let speed = classify_test name in
        test_case name speed (good_test typecheck_test name)) good_files);
    "typing-neg", (Stdlib.List.map (fun name ->
        let speed = classify_test name in
        test_case name speed (bad_test typecheck_test name)) bad_files);
  ]
