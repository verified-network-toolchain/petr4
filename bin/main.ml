(* Copyright 2019-present Cornell University
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy
 * of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
*)

open Core
open Petr4
open Common
open Lwt.Infix

exception ParsingError of string

let colorize colors s = ANSITerminal.sprintf colors "%s" s

module Conf: Parse_config = struct
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

module Parse = Make_parse(Conf)

open Parse

let parse_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Parse a P4 program"
    (empty
     +> flag "-v" no_arg ~doc:" Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> anon ("p4file" %: string))
    (fun verbose include_dir p4file () ->
      match parse_file include_dir p4file verbose with
      | `Ok _ ->
         ()
      | `Error (info, exn) ->
         Format.eprintf "%s: %s@\n%!" (Info.to_string info) (Exn.to_string exn))

let check_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Typecheck a P4 program"
    (empty
     +> flag "-v" no_arg ~doc:" Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> flag "-json" no_arg ~doc:" Print parsed tree as JSON"
     +> flag "-pretty" no_arg ~doc:" Pretty-print JSON"
     +> anon ("p4file" %: string))
    (fun verbose include_dir json pretty p4file () ->
       ignore (check_file include_dir p4file json pretty verbose))

let eval_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Run a P4 program"
    (empty
     +> flag "-v" no_arg ~doc:" Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> flag "-pkt-str" (required string) ~doc: "<pkt_str> Add packet string"
     +> flag "-ctrl-json" (required string) ~doc: "<ctrl_json> Add control json"
     +> flag "-port" (optional_with_default "0" string) ~doc: "<port_number> Specify ingress port"
     +> flag "-npts" (optional_with_default "0" string) ~doc: "<n> Speicify the number of ports connected to the switch"
     +> flag "-T" (optional_with_default "v1" string) ~doc: "<target> Specify P4 target (v1, ebpf currently supported)"
     +> anon ("p4file" %: string))
    (fun verbose include_dir pkt_str ctrl_json port target num_ports p4file () ->
       print_string (eval_file_string include_dir p4file verbose pkt_str (Yojson.Safe.from_file ctrl_json) (int_of_string port) (int_of_string num_ports) target))

let do_stf include_dir stf_file p4_file =
    let print_err (e_port, e_pkt) (a_port, a_pkt) =
        Printf.printf "Packet differed from the expected packet.\nExpected: port %s pkt %s\nActual:   port %s pkt %s\n\n"
                      e_port e_pkt a_port a_pkt
    in
    let print_ok (a_port, a_pkt) =
        Printf.printf "Packet matched the expected packet.\nPacket:   port %s pkt %s\n\n"
                      a_port a_pkt
    in
    let check_pkt (expected_pkt, actual_pkt) =
        if not (Petr4test.Test.packet_equal expected_pkt actual_pkt)
        then print_err expected_pkt actual_pkt
        else print_ok actual_pkt
    in
    let expected, results =
      Petr4test.Test.run_stf include_dir stf_file p4_file
    in
    let pkts = List.zip_exn expected results in
    List.iter ~f:check_pkt pkts

let stf_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Run a P4 program with an STF script"
    (empty
     +> flag "-v" no_arg ~doc:" Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> flag "-stf" (required string) ~doc: "<stf file> Select the .stf script to run"
     +> anon ("p4file" %: string))
    (fun verbose include_dir stf_file p4_file () ->
	 do_stf include_dir stf_file p4_file)

(**** Helper function ****)
let from_hex h =
  let buf = Buffer.create 101 in
  for i = 0 to String.length h / 2 - 1 do
    let d1 = h.[2 * i] in
    let d2 = h.[2 * i + 1] in
    Buffer.add_char buf (Hex.to_char d1 d2)
  done;
  Cstruct.of_string (Buffer.contents buf)
  
(***** Switch *****)
let entries : Prog.Value.entries ref = ref ([],[])

let do_insert (table:string) (matches:(string * string) list) (action:string) (action_data:(string * string) list) : unit = 
  let mk_num x : Ast.number_or_lpm = Ast.Num x in
  let mk_table : Ast.qualified_name = table in 
  let mk_priority : int option = None in
  let mk_matches : Ast.match_ list = List.map matches ~f:(fun (key,pat) -> (key, mk_num pat)) in 
  let mk_action : Ast.action = (action, action_data) in
  let mk_id : Ast.id option = None in
  let entry = (mk_priority, mk_matches, mk_action, mk_id) in
  let l1,l2 = !entries in 
  let old_entries = match List.Assoc.find l1 mk_table ~equal:String.(=) with None -> [] | Some l -> l in
  let l1' = List.Assoc.add l1 mk_table ~equal:String.(=) (entry::old_entries) in 
  entries := (l1',l2)
                                     
let ctrl_port : int = 510

type input =
  | Packet of int * Cstruct.t
  | Control of Runtime.ctrl_msg                    

let (input_stream, input_push) : input Lwt_stream.t * (input option -> unit) = Lwt_stream.create ()

let rec sock_loop (in_port,sock) : unit Lwt.t =
  let%bind packet = Lwt_rawlink.read_packet sock in
  let () = input_push (Some (Packet (in_port, packet))) in
  sock_loop (in_port,sock)
  
let send_packet sockets switch in_port (pkt,port) =
  let out_port = Bigint.to_int_exn port in
  if out_port = ctrl_port then
    let hex = Hex.of_cstruct pkt |> Hex.show in
    let () = Printf.eprintf "[Generating PacketIn %d %s\n%!]" in_port hex in
    Petr4_unix.Runtime_server.post_packet switch in_port hex
  else
    let () = Printf.eprintf "Sending packet from %d to %d\n%!" in_port out_port in 
    List.Assoc.find sockets out_port ~equal:Int.equal
    |> Option.value_map ~default:(Lwt.return ())
         ~f:(fun sock -> Lwt_rawlink.send_packet sock pkt)

let do_process_packet switch num_ports sockets env st pkt in_port = 
  let open Eval.V1Interpreter in 
  let ctrl = (!entries,[]) in
  let st',pkts = switch_packet ctrl env st pkt (Bigint.of_int in_port) (Bigint.of_int num_ports) in
  let%bind () = Lwt_list.iter_p (send_packet sockets switch in_port) pkts in
  Lwt.return st'

let do_counter_request switch st name index =
  let open Eval.V1Interpreter in
  Printf.eprintf "[Petr4] CounterRequest(%s,%d)\n%!" name index;
  let count = read_counter st name index in
  Petr4_unix.Runtime_server.post_counter_response switch name index count
  
let start_v1switch switch env prog sockets =
  let open Eval.V1Interpreter in 
  let (env, st) = init_switch env prog in

  (**** Asynchronously fetch inputs ****)
  let () = List.iter sockets ~f:(fun (in_port, sock) -> Lwt.ignore_result (sock_loop (in_port, sock))) in

  (**** Main loop ****)
  let rec loop st num_ports : unit Lwt.t =
    let%bind input = Lwt_stream.next input_stream in
    let%bind st' =
      match input with
      | Packet (in_port, packet) ->
         do_process_packet switch num_ports sockets env st packet in_port 
      | Control (Runtime.Insert { table; matches; action; action_data }) -> 
         do_insert table matches action action_data;
         Lwt.return st
      | Control (Runtime.PacketOut pkt_out) ->
         do_process_packet switch num_ports sockets env st (from_hex pkt_out.packet) (pkt_out.in_port)
      | Control (Runtime.CounterRequest req) ->
         let%bind () = do_counter_request switch st req.name req.index in
         Lwt.return st in
    loop st' num_ports in
  loop st (List.length sockets)
    
let start_switch verbose include_dir target pts switch p4_file =
  let f str =
    let pt_num, if_name = String.lsplit2_exn str ~on:'@' in
    String.strip pt_num |> Int.of_string, String.strip if_name in
  let ifnames = List.map ~f pts in
  let sockets = List.map ifnames
    ~f:(fun (pt_num, if_name) -> pt_num, Lwt_rawlink.open_link if_name) in
  match parse_file include_dir p4_file verbose with
  | `Ok prog ->
    let elab_prog, renamer = Elaborate.elab prog in
    let (cenv, typed_prog) =
      begin try Checker.check_program renamer elab_prog with
      | _ -> exit 1 end in
    let env = Env.CheckerEnv.eval_env_of_t cenv in
    begin match target with
      | "v1" -> start_v1switch switch env typed_prog sockets
      | _ -> failwith "mininet switches unsupported on this architecture" end      
  | `Error (info, exn) ->
    let exn_msg = Exn.to_string exn in
    let info_string = Info.to_string info in
    let () = Format.sprintf "%s\n%s" info_string exn_msg |> print_string in
    exit 1 |> Lwt.return

let handle_message (msg : Runtime.ctrl_msg) : unit =
  input_push (Some (Control msg))
    
let switch_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Set up a server that behaves as a P4-programmable switch"
    (empty
     +> flag "-v" no_arg ~doc: "Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> flag "-T" (optional_with_default "v1" string) ~doc: "<target> Specify P4 target (v1, ebpf currently supported)"
     +> flag "-i" (listed string) ~doc: "Specify the names by which the ports will be identified"
     +> flag "-switch" (optional_with_default "s0" string) ~doc: "Specify the switch identifier"
     +> anon ("p4file" %: string))
    (fun verbose include_dir target pts switch p4_file () ->
       let _ = Petr4_unix.Runtime_server.start switch ~handlers:handle_message () in
       start_switch verbose include_dir target pts switch p4_file |> Lwt_main.run)

let runtime_command = 
  let open Command.Spec in
  Command.basic_spec 
    ~summary: "Set up a dummy runtime server for testing"
    (empty 
     +> flag "-switch" (optional_with_default "s0" string) ~doc: "Specify the switch identifier")
    (fun switch () -> Petr4_unix.Runtime_server.start switch ~handlers:handle_message () |> Lwt_main.run)

let command =
  Command.group
    ~summary: "Petr4: A reference implementation of the P4_16 language"
    [ "parse", parse_command;
      "typecheck", check_command;
      "run", eval_command;
      "stf", stf_command;
      "switch", switch_command;
      "runtime", runtime_command;
    ]

let () = Command.run ~version: "0.1.2" command
