open Petr4
open Core
open P4stf.Test

let print pp = Format.printf "%a@." Pp.to_fmt pp

let parse_file include_dirs p4_file verbose =
  let () = Lexer.reset () in
  let () = Lexer.set_filename p4_file in
  let p4_string = Conf.preprocess include_dirs p4_file in
  let lexbuf = Lexing.from_string p4_string in
  try
    let prog = Parser.p4program Lexer.lexer lexbuf in
    if verbose then
      begin
        Format.eprintf "[%s] %s@\n%!" (Conf.green "Passed") p4_file;
        prog |> Pretty.format_program |> print;
        Format.print_string "@\n%!"; 
        Format.printf "----------@\n";
        Format.printf "%s@\n%!" (prog |> Types.program_to_yojson |> Yojson.Safe.pretty_to_string)
      end;
    `Ok prog
  with
  | err ->
    if verbose then Format.eprintf "[%s] %s@\n%!" (Conf.red "Failed") p4_file;
    `Error (Lexer.info lexbuf, err)


let main include_dir stf_tests_dir =
  get_stf_files stf_tests_dir
  |> List.map ~f:(fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    match parse_file include_dir p4_file false with
    | `Ok p4_prog -> stf_alco_test stf_file p4_file p4_prog
    | `Error e -> failwith ("petr4 couldn't parse the p4 prog" ^ p4_file))

let excl stf_tests_dir =
  get_stf_files stf_tests_dir
  |> List.map ~f:(fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    (Alcotest.test_case p4_file `Quick
      (fun () -> Alcotest.(check bool) p4_file true true)))

let () =
  ["p4c stf tests", main ["examples/"] "./examples/checker_tests/good/";
   "petr4 stf tests", main ["examples/"] "./p4stf/custom-stf-tests/";
   "excluded tests", excl "./examples/checker_tests/excluded/good/"]
  |> Alcotest.run "Stf-tests"
