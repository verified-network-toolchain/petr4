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
         Format.eprintf "%s: %s@\n%!" (P4info.to_string info) (Exn.to_string exn))

let check_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Typecheck a P4 program"
    (empty
     +> flag "-v" no_arg ~doc:" Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> flag "-exportp4" no_arg ~doc:" Export P4 syntax in Coq"
     +> flag "-exportp4-ocaml" no_arg ~doc:" Export P4 syntax in Ocaml"
     +> flag "-normalize" no_arg ~doc:" Simplify expressions in P4"
     +> flag "-export-file" (optional_with_default "out.v" string) ~doc:"Path to export P4 syntax in Coq"
     +> flag "-gen-loc" no_arg ~doc:" Generate locators in AST"
     +> flag "-printp4" no_arg ~doc:" Print checked syntax in P4"
     +> flag "-printp4cub" no_arg ~doc: "Print the p4cub AST"
     +> flag "-printp4-file" (optional_with_default "out.p4" string) ~doc:"Path to print checked syntax in P4"
     +> anon ("p4file" %: string))
    (fun verbose include_dir exportp4 exportp4_ocaml normalize export_file gen_loc printp4 printp4cub printp4_file p4file () ->
       ignore (check_file include_dir p4file exportp4 exportp4_ocaml normalize export_file gen_loc verbose printp4 printp4_file))

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
let compile_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "print the c file compiled using the HelloWorld.v file"
     (empty
     +> flag "-v" no_arg ~doc:" Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> flag "-normalize" no_arg ~doc:" Simplify expressions in P4"
     +> flag "-export-file" (optional_with_default "compiled.c" string)~doc:"Path to export compiled c file"
     +> flag "-gen-loc" no_arg ~doc:" Generate locators in AST"
     +> flag "-printp4cub" no_arg ~doc: "Print the p4cub AST"
     +> flag "-printp4-file" (optional_with_default "cubast.txt" string)~doc:"Path to print the p4cub syntax"
     +> anon ("p4file" %: string))
    (fun verbose include_dir normalize export_file gen_loc printp4cub printp4_file p4file () ->
       ignore (compile_file include_dir p4file normalize export_file verbose gen_loc printp4cub printp4_file))
let do_stf include_dir stf_file p4_file =
  failwith "do_stf removed"
  (* TODO restore stf
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
  *)


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

let command =
  Command.group
    ~summary: "Petr4: A reference implementation of the P4_16 language"
    [ "parse", parse_command;
      "typecheck", check_command;
      "compile", compile_command;
      "run", eval_command;
      "stf", stf_command ]

let () = Command.run ~version: "0.1.2" command
