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

let to_string pp : string =
  Format.fprintf Format.str_formatter "%a" Pp.to_fmt pp;
  Format.flush_str_formatter ()

let example_path l =
  let root = Filename.concat ".." "examples" in
  List.fold_left l ~init:root ~f:Filename.concat

let good_test f file () =
  Alcotest.(check bool) "good test" true
    (f ["../examples"] (example_path ["c_tests"; file]))

let get_files path =
  Sys.ls_dir path
  |> List.filter ~f:(fun name ->
      Core_kernel.Filename.check_suffix name ".p4")

let good_files = example_path ["c_tests"] |> get_files

let get_name include_dirs file =
  match Parse.parse_file include_dirs file false with 
  | `Ok prog -> prog |> C_mapping.format_program |> to_string 
  | `Error _ -> "121" 

let () = 
  Format.printf "%s" (get_name ["../examples"] (example_path ["c_tests"; "simple.p4"])); 
