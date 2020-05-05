open Ast
open Petr4
open Common
open Core_kernel

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

let strip_spaces s = s |> String.split_on_chars ~on:([' ']) |> String.concat ~sep:""

let evaler dirs name pkt_in port st =
  Petr4_parse.eval_file ("../examples":: dirs) name false pkt_in ctrl_json (Some st) port

let pp_string s = "\"" ^ s ^ "\""

let unimplemented_stmt = function
  | Packet(_, _) | Expect(_, _) -> false
  | _ -> true


let packet_equal (port_exp, p_exp) (port, p) =
  let (=) = Char.equal in
  let rec iter i =
    i >= String.length p_exp ||
    ((p_exp.[i] = p.[i] || p_exp.[i] = '*') && iter (i + 1))
    in
  String.(p_exp = p) && Int.(String.length p_exp = String.length p) && iter 0


let run_test dirs name stmts =
    match List.find ~f:unimplemented_stmt stmts with
    | Some _ -> failwith "unimplemented stf statement"
    | None ->
        let packets = List.filter_map ~f:(function Packet(port, packet)-> Some((int_of_string(port), packet |> String.lowercase)) | _ -> None) stmts in
        let results =
          List.fold_map
            ~init:Eval.V1Interpreter.empty_state
            ~f:(fun st (port, pkt) -> evaler dirs name pkt port st) packets |> snd |>
        List.filter_map ~f:(
          fun x -> match x with
          | `NoPacket -> None
          | `Error(info, exn) -> None
          | `Ok(pkt, port) ->
              let fixed =  pkt |> Cstruct.to_string |> Petr4_parse.hex_of_string |> strip_spaces |> String.lowercase in
              Some(fixed, Bigint.to_string port)
        )
          (* List.filter_map(fun x ->
          match x with `No_packet -> None
            | `Error(info, exn) -> Some("")
            | `Ok(pkt, port) -> Some("")) *)
        in
        let expected = List.filter_map ~f:(function Expect(port, Some(packet)) -> Some(packet, port) | _ -> None) stmts in
        List.zip_exn expected results |> List.iter ~f:(fun (p_exp, p) ->
          Alcotest.(testable (Fmt.pair Fmt.string Fmt.string) packet_equal |> check) "packet test" p_exp p)

let get_stf_files path =
  Core.Sys.ls_dir path |> Base.List.to_list |>
  List.filter ~f:(fun x -> Core.Filename.check_suffix x ".stf")

let stf_alco_test include_dir stf_file p4_file =
    let test = Alcotest.test_case p4_file `Quick (fun () ->
      let ic = In_channel.create stf_file in
      let lexbuf = Lexing.from_channel ic in
      let stmts = Test_parser.statements Test_lexer.token lexbuf in
      run_test include_dir p4_file stmts) in
    Filename.basename stf_file, [test]

let main include_dir stf_tests_dir =
  get_stf_files stf_tests_dir
  |> List.map ~f:( fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    stf_alco_test include_dir stf_file p4_file
    )

let () =
  main ["examples/"] "./examples/checker_tests/good/"
  (* main ["examples/"] "./stf-test/custom-stf-tests/" *)
  |> Alcotest.run "Stf-tests"
