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
     
let () =
  let open Alcotest in
  run "p4c checker_tests" [
      "good", [
        test_case "constants" `Quick (test_good_file ["/home/ryan/dev/p4c/p4include"] "/home/ryan/dev/petr4/examples/checker_tests/good/constants.p4");
      ]
    ]
