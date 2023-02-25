open Core
open P4stf.Test

(* This is a hack, sorry! *)
let known_failures =
  [
"recursive-casts";
"cast-senum";
"key-bmv2";
"issue2287-bmv2";
"equality-bmv2";
"table-entries-lpm-bmv2";
"issue1814-1-bmv2";
"match-on-exprs-bmv2";
"issue447-5-bmv2";
"issue447-4-bmv2";
"issue561-5-bmv2";
"issue561-4-bmv2";
"issue2153-bmv2";
"union1-bmv2";
"table-entries-ser-enum-bmv2";
"ternary2-bmv2";
"issue995-bmv2";
"constant-in-calculation-bmv2";
"v1model-const-entries-bmv2";
"issue561-2-bmv2";
"issue561-3-bmv2";
"issue655-bmv2";
"issue1879-bmv2";
"subparser-with-header-stack-bmv2";
"issue1768-bmv2";
"checksum2-bmv2";
"checksum3-bmv2";
"issue1097-2-bmv2";
"header-bool-bmv2";
"issue447-2-bmv2";
"issue447-3-bmv2";
"union2-bmv2";
"test-parserinvalidargument-error-bmv2";
"issue561-6-bmv2";
"issue561-7-bmv2";
"header-stack-ops-bmv2";
"issue1000-bmv2";
"table-entries-range-bmv2";
"runtime-index-2-bmv2";
"issue1755-1-bmv2";
"equality-varbit-bmv2";
"issue447-1-bmv2";
"table-entries-ternary-bmv2";
"flag_lost-bmv2";
"checksum1-bmv2";
"tlv";
"issue1566-bmv2";
"issue-2123-2-bmv2";
"issue-2123-3-bmv2";
"issue1824-bmv2";
"table-entries-priority-bmv2";
"array-copy-bmv2";
"issue1755-bmv2";
"table-entries-exact-ternary-bmv2";
"issue447-bmv2";
"parser_error-bmv2";
"issue561-1-bmv2";
"issue1025-bmv2";
"error";
"int";
"stack";
"issue235";
"dynamic";
"table3";
"exit";
"table2";
"hash_identity";
"named-arg-copy-out";
"subcontrol";
"named-arg";
"error2";
"switch-stmt";
"bitstring_slices";
"issue396-1";
"register";
"out_params";
"equality";
"counter";
"extraction"
  ]

let classify_test name =
  if List.mem ~equal:String.equal known_failures name
  then `Slow
  else `Quick

let main include_dir stf_tests_dir =
  get_stf_files stf_tests_dir
  |> List.map ~f:(fun x ->
    let basename = Stdlib.Filename.remove_extension x in
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    stf_alco_test (classify_test basename) include_dir stf_file p4_file)

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
