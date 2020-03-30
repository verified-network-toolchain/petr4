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

let parser_test include_dirs file = 
  match Parse.parse_file include_dirs file false with 
  | `Ok _ -> true
  | `Error _ -> false

let typecheck_test (include_dirs : string list) (p4_file : string) : bool =
  match Parse.parse_file include_dirs p4_file false with
  | `Ok prog ->
    let prog = Elaborate.elab prog in
    Checker.check_program prog |> ignore; true
  | `Error (info, Lexer.Error s) ->
    (*Format.eprintf "%s: %s@\n%!" (Info.to_string info) s;*) false
  | `Error (info, Parser.Error) ->
    (*Format.eprintf "%s: syntax error@\n%!" (Info.to_string info);*) false
  | `Error (info, err) ->
    (*Format.eprintf "%s: %s@\n%!" (Info.to_string info) (Exn.to_string err);*) false

let _ = 
  Sys.chdir Filename.parent_dir_name;
  Sys.chdir Filename.parent_dir_name;
  Sys.chdir Filename.parent_dir_name; 
  Sys.chdir "test"

let path name =
  Filename.concat "examples" name

let%test _ = parser_test [] (path "core.p4")
let%test _ = parser_test ["examples"] (path "ebpf_model.p4")
let%test _ = parser_test ["examples"] (path "hello_world.p4")
let%test _ = parser_test ["examples"] (path "helloWorld.p4")
let%test _ = parser_test [] (path "simple.p4")
let%test _ = parser_test ["examples"] (path "v1model.p4")
let%test _ = parser_test ["examples"] (path "xdp_model.p4")

let%test _ = typecheck_test [] (path "after-return.p4")
let%test _ = typecheck_test [] (path "alias.p4")
let%test _ = typecheck_test ["examples"] (path "annotation-bug.p4")
let%test _ = typecheck_test ["examples"] (path "arch1.p4")
let%test _ = typecheck_test [] (path "array_field1.p4")
let%test _ = typecheck_test ["examples"] (path "basic_routing-bmv2.p4")
let%test _ = typecheck_test [] (path "bitExtract.p4")
let%test _ = typecheck_test ["examples"] (path "calc-ebpf.p4")
let%test _ = typecheck_test [] (path "cast-call.p4")
let%test _ = typecheck_test [] (path "concat-fold.p4")
let%test _ = typecheck_test [] (path "const.p4")
let%test _ = typecheck_test [] (path "constsigned.p4")
let%test _ = typecheck_test [] (path "core.p4")
let%test _ = typecheck_test ["examples"] (path "crc32-bmv2.p4")
let%test _ = typecheck_test [] (path "deadcode.p4")
let%test _ = typecheck_test [] (path "decl2.p4")
let%test _ = typecheck_test [] (path "default-control-argument.p4")
let%test _ = typecheck_test [] (path "default-package-argument.p4")
let%test _ = typecheck_test ["examples"] (path "default.p4")
let%test _ = typecheck_test ["examples"] (path "ebpf_model.p4")
let%test _ = typecheck_test [] (path "enum-folding.p4")
let%test _ = typecheck_test [] (path "exit1.p4")
let%test _ = typecheck_test [] (path "exit2.p4")
let%test _ = typecheck_test [] (path "fold_match.p4")
let%test _ = typecheck_test ["examples"] (path "functors2.p4")
let%test _ = typecheck_test ["examples"] (path "functors8.p4")
let%test _ = typecheck_test [] (path "generic_fun.p4")
let%test _ = typecheck_test [] (path "generic.p4")
let%test _ = typecheck_test [] (path "hashext.p4")
let%test _ = typecheck_test ["examples"] (path "hello_world.p4")
let%test _ = typecheck_test ["examples"] (path "helloWorld.p4")
let%test _ = typecheck_test ["examples"] (path "index.p4")
let%test _ = typecheck_test [] (path "inline-control1.p4")
let%test _ = typecheck_test [] (path "inline.p4")
let%test _ = typecheck_test [] (path "intType.p4")
let%test _ = typecheck_test [] (path "issue47.p4")
let%test _ = typecheck_test ["examples"] (path "issue232-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue281.p4")
let%test _ = typecheck_test [] (path "issue344.p4")
let%test _ = typecheck_test ["examples"] (path "issue355-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue356-bmv2.p4")
let%test _ = typecheck_test [] (path "issue396.p4")
let%test _ = typecheck_test ["examples"] (path "issue430-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue584-1.p4")
let%test _ = typecheck_test ["examples"] (path "issue803-2.p4")
let%test _ = typecheck_test ["examples"] (path "issue870_ebpf.p4")
let%test _ = typecheck_test ["examples"] (path "issue933-1.p4")
let%test _ = typecheck_test ["examples"] (path "issue933.p4")
let%test _ = typecheck_test ["examples"] (path "issue995-bmv2.p4")
let%test _ = typecheck_test [] (path "issue1006.p4")
let%test _ = typecheck_test ["examples"] (path "issue1097-2-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1097-bmv2.p4")
let%test _ = typecheck_test [] (path "issue1210.p4")
let%test _ = typecheck_test ["examples"] (path "issue1291-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1304.p4")
let%test _ = typecheck_test ["examples"] (path "issue1333.p4")
let%test _ = typecheck_test [] (path "issue1334.p4")
let%test _ = typecheck_test [] (path "issue1452-1.p4")
let%test _ = typecheck_test [] (path "issue1452.p4")
let%test _ = typecheck_test ["examples"] (path "issue1517-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1538.p4")
let%test _ = typecheck_test [] (path "issue1586.p4")
let%test _ = typecheck_test ["examples"] (path "issue1638.p4")
let%test _ = typecheck_test ["examples"] (path "issue1653-complex-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1713-bmv2.p4")
let%test _ = typecheck_test [] (path "issue1717.p4")
let%test _ = typecheck_test ["examples"] (path "issue1768-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1781-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1814-1-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1814-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1879-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1937-1-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1937-2-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1937-3-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "issue1937.p4")
let%test _ = typecheck_test [] (path "list-compare.p4")
let%test _ = typecheck_test ["examples"] (path "mask.p4")
let%test _ = typecheck_test ["examples"] (path "match.p4")
let%test _ = typecheck_test ["examples"] (path "mux-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "named-arg1.p4")
let%test _ = typecheck_test [] (path "names.p4")
let%test _ = typecheck_test ["examples"] (path "nested_select.p4")
let%test _ = typecheck_test [] (path "nested-tuple.p4")
let%test _ = typecheck_test [] (path "octal.p4")
let%test _ = typecheck_test ["examples"] (path "parser-locals2.p4")
let%test _ = typecheck_test [] (path "precedence.p4")
let%test _ = typecheck_test ["examples"] (path "pvs-nested-struct.p4")
let%test _ = typecheck_test ["examples"] (path "pvs.p4")
let%test _ = typecheck_test ["examples"] (path "rcp.p4")
let%test _ = typecheck_test ["examples"] (path "select-struct.p4")
let%test _ = typecheck_test ["examples"] (path "serenum.p4")
let%test _ = typecheck_test [] (path "side_effects.p4")
let%test _ = typecheck_test [] (path "simple.p4")
let%test _ = typecheck_test [] (path "spec-ex04.p4")
let%test _ = typecheck_test [] (path "spec-ex14.p4")
let%test _ = typecheck_test ["examples"] (path "spec-ex15.p4")
let%test _ = typecheck_test ["examples"] (path "spec-ex18.p4")
let%test _ = typecheck_test [] (path "specialization.p4")
let%test _ = typecheck_test [] (path "strength.p4")
let%test _ = typecheck_test ["examples"] (path "strength4.p4")
let%test _ = typecheck_test [] (path "struct_init.p4")
let%test _ = typecheck_test [] (path "struct1.p4")
let%test _ = typecheck_test [] (path "structArg.p4")
let%test _ = typecheck_test ["examples"] (path "subparser-with-header-stack-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "table-entries-range-bmv2.p4")
let%test _ = typecheck_test ["examples"] (path "table-key-serenum.p4")
let%test _ = typecheck_test [] (path "ternary2-bmv2.p4")
let%test _ = typecheck_test [] (path "tuple0.p4")
let%test _ = typecheck_test [] (path "twoPipe.p4")
let%test _ = typecheck_test [] (path "type-params.p4")
let%test _ = typecheck_test ["examples"] (path "unused.p4")
let%test _ = typecheck_test ["examples"] (path "v1model-digest-containing-ser-enum.p4")
let%test _ = typecheck_test ["examples"] (path "v1model-p4runtime-most-types1.p4")
let%test _ = typecheck_test [] (path "v1model.p4")
let%test _ = typecheck_test [] (path "version.p4")
let%test _ = typecheck_test ["examples"] (path "xdp_model.p4")
