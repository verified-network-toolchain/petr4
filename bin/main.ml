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
     +> flag "-T" (optional_with_default "v1" string) ~doc: "<target> Specify P4 target (v1, ebpf currently supported)"
     +> anon ("p4file" %: string))
    (fun verbose include_dir pkt_str ctrl_json port target p4file () ->
       print_string (eval_file_string include_dir p4file verbose pkt_str (Yojson.Safe.from_file ctrl_json) (int_of_string port) target))

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

let start_v1switch env prog sockets =
  let open Eval in
  let open V1Interpreter in
  let (env, st) = init_switch env prog in
  let rec loop ctrl st =
    let st, pkts =
      List.map sockets ~f:(fun sock -> sock, Bytes.create 1024)
      |> List.map
        ~f:(fun (sock, buf) -> buf, Unix.recv sock ~buf ~pos:0 ~len:1024 ~mode:[])
      |> List.map
        ~f:(fun (buf, len) -> String.sub (Bytes.to_string buf) ~pos:0 ~len)
      |> List.map
        ~f:(fun pkt -> Cstruct.of_string pkt)
      |> List.fold_mapi
        ~init:st
        ~f:(fun i st pkt -> switch_packet ctrl env st pkt (Bigint.of_int i)) in
    let () =
      List.filter_map pkts ~f:Fn.id
      |> List.map ~f:(fun (pkt, pt) -> Cstruct.to_string pkt, Bigint.to_int_exn pt)
      |> List.map ~f:(fun (pkt, pt) -> pkt, List.nth sockets pt)
      |> List.filter_map ~f:(fun (pkt, pt) -> Option.map pt ~f:(fun pt -> pkt, pt))
      |> List.map ~f:(fun (buf, pt) -> Unix.send_substring pt ~buf ~pos:0 ~len:(String.length buf) ~mode:[])
      |> List.iter ~f:ignore in
    loop ctrl st in
  loop (([],[]), []) st
  (* inifinite loop - non-blocking recv?; call petr4 interpreter; sento call *)

let start_switch verbose include_dir target n pts p4_file =
  (* List.iter sockets ~f:(Unix.listen ~backlog:1); *)
  (* List.iter sockets ~f:(fun sock -> Unix.accept sock |> ignore); *)
  (* TODO: set socket options for timeout on recv? *)
  (* TODO: add a control plane socket *)
  (* let rec loop () =
    let sock = Lwt_rawlink.open_link "tap1" in
    let buf = Lwt_rawlink.read_packet sock in
    buf >>= fun cstruct ->
      let msg = Cstruct.to_string cstruct in
      Format.sprintf "packet: %s" msg |> print_endline;
      Lwt.return () >>= loop in
  loop () *)
  let sock = Lwt_rawlink.open_link "tap0" in
  let msg = Cstruct.of_string "Hi; maybe the packet is too short so im spamming characters in here blah blah" in
  Lwt_rawlink.send_packet sock msg >>= fun _ ->
  Lwt_rawlink.close_link sock
  (* match parse_file include_dir p4_file verbose with
  | `Ok prog ->
    let elab_prog, renamer = Elaborate.elab prog in
    let (cenv, typed_prog) = Checker.check_program renamer elab_prog in
    let env = Env.CheckerEnv.eval_env_of_t cenv in
    begin match target with
      | "v1" -> start_v1switch env typed_prog sockets
      | _ -> failwith "mininet switches unsupported on this architecture" end      
  | `Error (info, exn) ->
    let exn_msg = Exn.to_string exn in
    let info_string = Info.to_string info in
    Format.sprintf "%s\n%s" info_string exn_msg |> print_string *)

let switch_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Set up a server that behaves as a P4-programmable switch"
    (empty
     +> flag "-v" no_arg ~doc: "Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> flag "-T" (optional_with_default "v1" string) ~doc: "<target> Specify P4 target (v1, ebpf currently supported)"
     +> flag "-n" (optional_with_default 0 int) ~doc: "Specify the number of ports with which to set up the switch"
     +> flag "-p" (listed string) ~doc: "Specify the names by which the port will be identified"
     +> anon ("p4file" %: string))
    (fun verbose include_dir target n pts p4_file () ->
	 start_switch verbose include_dir target n pts p4_file |> Lwt_main.run)

let command =
  Command.group
    ~summary: "Petr4: A reference implementation of the P4_16 language"
    [ "parse", parse_command;
      "typecheck", check_command;
      "run", eval_command;
      "stf", stf_command;
      "switch", switch_command; ]

let () = Command.run ~version: "0.1.2" command
