open Core
open Petr4

let preprocess include_dirs p4file =
  let cmd =
    String.concat ~sep:" "
      (["cc"] @
       (List.map include_dirs ~f:(Printf.sprintf "-I%s") @
        ["-undef"; "-nostdinc"; "-E"; "-x"; "c"; p4file])) in
  let in_chan = Unix.open_process_in cmd in
  let str = In_channel.input_all in_chan in
  let _ = Unix.close_process_in in_chan in
  if String.length str < 1
  then raise_s [%message "no output from preprocessor?"]
  else str

let check_file include_dirs p4_file =
  let () = Lexer.reset () in
  let () = Lexer.set_filename p4_file in
  let p4_string = preprocess include_dirs p4_file in
  let lexbuf = Lexing.from_string p4_string in
  let prog = Parser.p4program Lexer.lexer lexbuf in
  prog |> Elaborate.elab |> Checker.check_program |> ignore;
  true

let test_good_file include_dirs p4_file () =
  Alcotest.(check bool) "file typechecks" true (check_file include_dirs p4_file)

let test_bad_file include_dirs p4_file () =
  Alcotest.(check bool) "file does not typecheck" false
    begin
      try check_file include_dirs p4_file
      with _ -> false
    end
              
let make_case base_dir testfn filename =
  let include_dirs = ["examples"]
  in
  Alcotest.test_case filename `Quick
    (testfn include_dirs (Filename.concat base_dir filename))

let () =
  let is_p4 f = String.is_suffix ~suffix:".p4" f in
  let good_dir = "examples/checker_tests/good_mini" in
  let good_tests =
    Sys.readdir good_dir
    |> Array.filter ~f:is_p4
    |> Array.map ~f:(make_case good_dir test_good_file)
    |> Array.to_list
  in
  (*
  let bad_dir = "examples/checker_tests/bad" in
  let bad_tests =
    Sys.readdir bad_dir
    |> Array.filter ~f:is_p4
    |> Array.map ~f:(make_case bad_dir test_bad_file)
    |> Array.to_list
  in
   *)
  Alcotest.run "p4c checker_tests" [
      "good", good_tests;
      (*"bad", bad_tests*)
    ]
