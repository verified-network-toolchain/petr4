open Core
(*TODO restore stf tests
open Petr4test.Test
*)

let main include_dir stf_tests_dir =
  failwith "tests unimplemented"
  (*TODO restore stf tests
  get_stf_files stf_tests_dir
  |> List.map ~f:(fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    stf_alco_test include_dir stf_file p4_file)
  *)

let excl stf_tests_dir =
  failwith "tests unimplemented"
  (*TODO restore stf tests
  get_stf_files stf_tests_dir
  |> List.map ~f:(fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    (Alcotest.test_case p4_file `Quick
      (fun () -> Alcotest.(check bool) p4_file true true)))
  *)

let () =
  ["p4c stf tests", main ["examples/"] "./examples/checker_tests/good/";
   "petr4 stf tests", main ["examples/"] "./stf-test/custom-stf-tests/";
   "excluded tests", excl "./examples/checker_tests/excluded/good/"]
  |> Alcotest.run "Stf-tests"
