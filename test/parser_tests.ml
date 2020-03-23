open Core
open Petr4
open Common

module Conf = struct
  let red s = s
  let green s = s

  let preprocess include_dirs p4file =
    let buf = Buffer.create 101 in
    let env = P4pp.Eval.{ file = p4file ; defines = []} in
    ignore (P4pp.Eval.preprocess_file [] env buf p4file);
    Buffer.contents buf
end

module Parse = Make_parse(Conf)

let parser_test file = 
  match Parse.parse_file [] file false with 
  | `Ok _ -> true
  | `Error _ -> false

let rec get_parse_files parse_dir dir_handle acc =
  match Unix.readdir_opt dir_handle with
  | Some ".."
  | Some "." -> get_parse_files parse_dir dir_handle acc
  | Some file -> 
    begin
      let path = Filename.concat parse_dir file in 
      get_parse_files parse_dir dir_handle (path::acc)
    end
  | None -> acc

let parser_files = 
  Sys.chdir Filename.parent_dir_name;
  Sys.chdir Filename.parent_dir_name;
  Sys.chdir Filename.parent_dir_name;
  let test_dir = Filename.concat (Sys.getcwd ()) "test" in
  let parse_dir = Filename.concat test_dir "parse" in
  let dir = Unix.opendir parse_dir in
  get_parse_files parse_dir dir []

let rec make_parse_tests files =
  match files with
  | h::[] -> parser_test h
  | h::t -> ignore (parser_test h); make_parse_tests t
  | [] -> true

let%test _ = 
  Format.printf "%s@\n%!" (Sys.getcwd ());
  make_parse_tests parser_files
