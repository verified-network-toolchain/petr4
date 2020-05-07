open Ast
open Petr4
open Common

let stmt_string s =
  match s with
  | Expect(port, Some(expect)) ->
    "port: " ^ port ^" expect: " ^ expect
  | Packet(port, packet) ->
    "port: " ^ port ^" packet: " ^ packet
  | _ -> failwith "unimplemented"


let colorize colors s = ANSITerminal.sprintf colors "%s" s

module Conf: Parse_config =
struct
  open Core
  let red s = colorize [ANSITerminal.red] s
  let green s = colorize [ANSITerminal.green] s

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

module Petr4_parse = Make_parse(Conf)

let empty_ctrl =
{|{
  "pre_entries": [],
  "matches": []
  }
|}

let ctrl_json = Yojson.Safe.from_string empty_ctrl

let strip_spaces s = s |> String.split_on_char ' ' |> String.concat ""

let evaler dirs name pkt_in =
  Petr4_parse.eval_file ("../examples":: dirs) name false pkt_in ctrl_json |> strip_spaces

let pp_string s = "\"" ^ s ^ "\""

let unimplemented_stmt = function
  | Packet(_, _) | Expect(_, _) -> false
  | _ -> true


let packet_equal p_exp p =
  let rec iter i =
    i >= String.length p_exp ||
    ((p_exp.[i] = p.[i] || p_exp.[i] = '*') && iter (i + 1))
    in
  String.(length p_exp = length p) && iter 0


let run_test dirs name stmts =
    match List.find_opt unimplemented_stmt stmts with
    | Some _ -> failwith "unimplemented stf statement"
    | None ->
        let packets = List.filter_map (function Packet(port, packet)-> Some(packet) | _ -> None) stmts in
        let results = List.map (evaler dirs name) packets in
        let expected = List.filter_map (function Expect(port, Some(packet)) -> Some(packet) | _ -> None) stmts in
        List.combine expected results |> List.iter (fun (p_exp, p) ->
          Alcotest.(testable Fmt.string packet_equal |> check) "packet test" p_exp p)

let get_stf_files path =
  Core.Sys.ls_dir path |> Base.List.to_list |>
  List.filter (fun x -> Core.Filename.check_suffix x ".stf")

let stf_alco_test include_dir stf_file p4_file =
    let test = Alcotest.test_case p4_file `Quick (fun () ->
      let ic = open_in stf_file in
      let lexbuf = Lexing.from_channel ic in
      let stmts = Test_parser.statements Test_lexer.token lexbuf in
      run_test include_dir p4_file stmts) in
    Filename.basename stf_file, [test]

let main include_dir stf_tests_dir =
  get_stf_files stf_tests_dir
  |> List.map ( fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Filename.remove_extension stf_file ^ ".p4" in
    stf_alco_test include_dir stf_file p4_file
    )

let () =
  main ["examples/"] "./examples/checker_tests/good/" @
  main ["examples/"] "./stf-test/custom-stf-tests/"
  |> Alcotest.run "Stf-tests"