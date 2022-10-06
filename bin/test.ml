open Core
open Petr4test.Test

module UnixIO : Petr4.Common.DriverIO = struct
  let colorize colors s = ANSITerminal.sprintf colors "%s" s
  let red s = colorize [ANSITerminal.red] s
  let green s = colorize [ANSITerminal.green] s
  
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

  let open_file path =
    Core_unix.open_process_out path

  let close_file ochan =
    match Core_unix.close_process_out ochan with
    | Ok () -> ()
    | Error _ -> failwith "Error in close_file"
  
end

module UnixDriver = Petr4.Common.MakeDriver(UnixIO)

let main include_dir stf_tests_dir =
  get_stf_files stf_tests_dir
  |> List.map ~f:(fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    let cfg = Petr4.Pass.mk_parse_only include_dir p4_file in
    let open Result in
    match UnixDriver.(preprocess cfg >>= lex cfg >>= parse cfg) with
    | Ok p4_prog ->
       stf_alco_test stf_file p4_file p4_prog
    | Error e ->
       failwith "error while parsing stf test.")

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
