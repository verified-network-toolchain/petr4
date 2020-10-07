open Petr4.Ast
open Petr4.Test_stf

let main include_dir stf_tests_dir =
  get_stf_files stf_tests_dir
  |> List.map ~f:( fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    stf_alco_test include_dir stf_file p4_file
    |> Alcotest.run
    |> Alcotest.run "petr4-test"
    )

let () =
  main ["examples/"] "./examples/checker_tests/good/" @
  main ["examples/"] "./stf-test/custom-stf-tests/"
  |> Alcotest.run "Stf-tests"
