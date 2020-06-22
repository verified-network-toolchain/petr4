open Petr4
open Petr4.Ast
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

let evaler dirs name pkt_in port st add =
  Petr4_parse.eval_file ("../examples":: dirs) name false pkt_in add ctrl_json (Some st) port

let pp_string s = "\"" ^ s ^ "\""

let unimplemented_stmt = function
  | Packet(_, _) | Expect(_, _) -> false
  | _ -> true

let packet_equal (port_exp, pkt_exp) (port, pkt) =
  let (=) = Char.equal in
  let rec iter i =
    i >= String.length pkt_exp ||
    ((pkt_exp.[i] = pkt.[i] || pkt_exp.[i] = '*') && iter (i + 1))
    in
    String.(port_exp = port) && Int.(String.length pkt_exp = String.length pkt) && iter 0

let convert_qualified name =
  match String.rindex name '.' with 
  | None -> name
  | Some idx -> 
    let length = String.length name in
    String.slice name (idx + 1) length

let rec run_test' dirs name stmts add results expected st = 
  match stmts with
  | [] -> 
    List.zip_exn expected results |> List.iter ~f:(fun (p_exp, p) ->
          Alcotest.(testable (Fmt.pair ~sep:Fmt.sp Fmt.string Fmt.string) packet_equal |> check) "packet test" p_exp p)
  | hd :: tl -> 
    match hd with
    | Packet (port, packet) -> 
      let (st', result) = evaler dirs name (packet |> String.lowercase) (int_of_string port) st add in
      let results' =
      begin match result with
      | `Ok(pkt, port) ->
              let fixed =  pkt |> Cstruct.to_string |> Petr4_parse.hex_of_string |> strip_spaces |> String.lowercase in
              (Bigint.to_string port, fixed) :: results
      | _ -> results
      end in
      run_test' dirs name tl add results' expected st'
    | Expect (port, Some packet) -> run_test' dirs name tl add results ((port, strip_spaces packet |> String.lowercase) :: expected) st
    | Add (tbl_name, priority, match_list, (action_name, args), id) ->
      let tbl_name' = convert_qualified tbl_name in 
      let action_name' = convert_qualified action_name in
      let add' =
      begin match List.findi add ~f:(fun _ (n,_) -> String.(n = tbl_name')) with
      | None ->
        (tbl_name', [(priority, match_list, (action_name', args), id)]) :: add
      | Some (index, entries_info) ->
        let xs, ys = List.split_n add index in
        match ys with
        | y :: ys -> xs @ (tbl_name', (priority, match_list, (action_name', args), id) :: snd entries_info) :: ys
        | [] -> failwith "unreachable: index out of bounds"
      end in 
      run_test' dirs name tl add' results expected st
    | Wait -> Unix.sleep 1; run_test' dirs name tl add results expected st
    | _ -> failwith "unimplemented stf statement"

let get_stf_files path =
  Core.Sys.ls_dir path |> Base.List.to_list |>
  List.filter ~f:(fun x -> Core.Filename.check_suffix x ".stf")

let stf_alco_test include_dir stf_file p4_file =
    let test = Alcotest.test_case p4_file `Quick (fun () ->
      let ic = In_channel.create stf_file in
      let lexbuf = Lexing.from_channel ic in
      let stmts = Test_parser.statements Test_lexer.token lexbuf in
      run_test' include_dir p4_file stmts [] [] [] Eval.V1Interpreter.empty_state) in
    Filename.basename stf_file, [test]

let main include_dir stf_tests_dir =
  get_stf_files stf_tests_dir
  |> List.map ~f:( fun x ->
    let stf_file = Filename.concat stf_tests_dir x in
    let p4_file = Stdlib.Filename.remove_extension stf_file ^ ".p4" in
    stf_alco_test include_dir stf_file p4_file
    )

let () =
  main ["examples/"] "./examples/checker_tests/good/" @
  main ["examples/"] "./stf-test/custom-stf-tests/"
  |> Alcotest.run "Stf-tests"