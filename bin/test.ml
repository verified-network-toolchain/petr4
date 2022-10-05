open Core
open Petr4test.Test

module Conf: Petr4.Common.Parse_config = struct
  let red s = s
  let green s = s

  let preprocess include_dirs p4file =
    let cmd =
      String.concat ~sep:" "
        (["cc"] @
         (List.map include_dirs ~f:(Printf.sprintf "-I%s") @
          ["-undef"; "-nostdinc"; "-E"; "-x"; "c"; p4file])) in
    let in_chan = Core_unix.open_process_in cmd in
    let str = In_channel.input_all in_chan in
    let _ = Core_unix.close_process_in in_chan in
    str
end

module Parse = Petr4.Common.Make_parse(Conf)

let main include_dir stf_tests_dir =
  get_stf_files stf_tests_dir
  |> List.map ~f:(fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    match Parse.parse_file include_dir p4_file false with
    | `Ok p4_prog -> stf_alco_test stf_file p4_file p4_prog
    | `Error (info, exn) ->
       Format.eprintf "%s: %s@\n%!"
         (Petr4.P4info.to_string info)
         (Core.Exn.to_string exn);
       failwith "Parse error while loading STF tests. Exiting")

let excl stf_tests_dir =
  get_stf_files stf_tests_dir
  |> List.map ~f:(fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    (Alcotest.test_case p4_file `Quick
      (fun () -> Alcotest.(check bool) p4_file true true)))

let () =
  ["p4c stf tests", main ["examples/"] "./examples/checker_tests/good/";
   "petr4 stf tests", main ["examples/"] "./stf-test/custom-stf-tests/";
   "excluded tests", excl "./examples/checker_tests/excluded/good/"]
  |> Alcotest.run "Stf-tests"
