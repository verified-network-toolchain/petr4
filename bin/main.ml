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
open Common

module Conf: Parse_config = struct
  let colorize colors s = ANSITerminal.sprintf colors "%s" s
  let red s = colorize [ANSITerminal.red] s
  let green s = colorize [ANSITerminal.green] s
  let preprocess include_dirs p4file =
    let env = P4pp.Eval.empty "" include_dirs [] in
    let p4file_contents = In_channel.(with_file p4file ~f:input_all) in
    let str,_ = P4pp.Eval.FileSystem.preprocess env p4file p4file_contents in
    str
end

open Make_parse(Conf)

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
      "run", eval_command;
      "stf", stf_command ]

let () = Command.run ~version: "0.1.2" command
