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

let%test _ = 
  Format.printf "%s@\n%!" (Sys.getcwd ());
  parser_test "simple.p4"
