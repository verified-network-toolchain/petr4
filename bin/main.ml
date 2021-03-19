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

(* This belongs in lib/common.ml, but it uses the Unix module. Since
   lib/ all has to be javascript-compilable and js_of_ocaml cannot
   translate the Unix API, it's here instead. *)
let cc include_dirs contents =
  let include_flags =
    include_dirs
    |> List.map ~f:(fun d -> "-I " ^ d)
    |> String.concat
  in
  let cmd = Printf.sprintf "cc -x c -c -o p4prog.o %s -" include_flags in
  let cc_stdin = Core.Unix.open_process_out cmd in
  Common.fprint cc_stdin contents;
  Core.Unix.close_process_out cc_stdin

let ccomp_command =
  let open Command.Spec in
  Command.basic_spec ~summary:"Compile a P4 program to C"
    (empty
     +> flag "-v" no_arg ~doc:" Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> flag "-i" (listed string) ~doc:"<dir> Add directory to C include search path"
     +> flag "-c" no_arg ~doc:"Enable cc compilation"
     +> anon ("p4file" %: string))
    (fun verbose include_dirs c_include_dirs yes_cc p4_file () ->
       if yes_cc
       then ccomp_file verbose include_dirs p4_file |> cc c_include_dirs |> ignore
       else ccomp_file verbose include_dirs p4_file |> Common.print)

let command =
  Command.group
    ~summary: "Petr4: A reference implementation of the P4_16 language"
    [ "parse", parse_command;
      "typecheck", check_command;
      "run", eval_command;
      "stf", stf_command;
      "ccomp", ccomp_command ]

let () = Command.run ~version: "0.1.2" command
