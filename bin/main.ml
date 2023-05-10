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

let parse_ext_flag p = Pass.Run (Option.map p ~f:Pass.parse_output_exn)

let parse_backend unroll_parsers output_gcl output_clight =
  match output_gcl, output_clight with
  | Some gcl, None ->
    let message = "please provide a depth with -unroll-parsers when compiling to GCL" in
    let depth = Option.value_exn unroll_parsers ~message in
    let gcl_output = Pass.parse_output_exn gcl in
    Pass.Run (Pass.GCLBackend {depth; gcl_output})
  | None, Some clight ->
    let clight_output = Pass.parse_output_exn clight in
    Pass.Run (Pass.CBackend clight_output)
  | Some _, Some _ ->
    failwith "Can produce either C or GCL but not both."
  | None, None ->
    Pass.Skip

let parser_flags : Pass.parser_cfg Command.Param.t =
  let open Command.Let_syntax in
  [%map_open
    let verbose = flag "-v" no_arg ~doc:"Be more verbose."
    and includes = flag "-I" (listed string)
        ~doc:"dir Paths to search for files sourced with #include directives."
    and infile = anon ("file.p4" %: string)
    in
    Pass.{ cfg_infile = infile;
           cfg_includes = includes;
           cfg_verbose = verbose }]

let checker_flags : Pass.checker_cfg Command.Param.t =
  let open Command.Let_syntax in
  [%map_open
    let cfg_parser = parser_flags
    and normalize = flag "-normalize" no_arg
        ~doc:"Simplify expressions."
    and gen_loc = flag "-gen-loc" no_arg
        ~doc:"Infer locators in P4light after typechecking."
    and output_p4surface = flag "-output-p4surface" (optional string)
        ~doc:"file Output P4surface to the specified file."
    and output_p4light = flag "-output-p4light" (optional string)
        ~doc:"file Output P4light to the specified file."
    in
    Pass.{ cfg_parser;
           cfg_p4surface = parse_ext_flag output_p4surface;
           (* normalize must come before gen_loc *)
           cfg_normalize = Pass.cfg_of_bool normalize;
           cfg_gen_loc   = Pass.cfg_of_bool gen_loc;
           cfg_p4light   = parse_ext_flag output_p4light }]


let compiler_flags : Pass.compiler_cfg Command.Param.t =
  let open Command.Let_syntax in
  [%map_open 
    let cfg_checker = checker_flags
    and output_p4cub = flag "-output-p4cub" (optional string)
        ~doc:"file Output P4Cub to the specified file."
    and unroll_parsers = flag "-unroll-parsers" (optional int)
        ~doc:"depth Unroll parsers to given depth."
    and output_p4flat = flag "-output-p4flat" (optional string)
        ~doc:"file Output P4flat to the specified file."
    and output_gcl = flag "-output-gcl" (optional string)
        ~doc:"file Output GCL to the specified file."
    and output_c = flag "-output-c" (optional string)
        ~doc:"file Output C to the specified file."
    in
    Pass.{ cfg_checker;
           cfg_p4cub   = parse_ext_flag output_p4cub;
           cfg_p4flat  = parse_ext_flag output_p4flat;
           cfg_backend = parse_backend unroll_parsers output_gcl output_c; }
  ]

let interp_flags : Pass.interpreter_cfg Command.Param.t =
  let open Command.Let_syntax in
  [%map_open
    let cfg_checker = checker_flags
    and stf_file = flag "-stf" (optional string)
        ~doc:"file to read STF from"
    and packet = flag "-pkt" (optional string)
        ~doc:"packet in hex form"
    and port = flag "-port" (optional int)
        ~doc:"input port for packet"
    in
    match stf_file, packet, port with
    | Some stf_file, None, None ->
      Pass.{ cfg_checker;
             cfg_inputs = InputSTF stf_file; }
    | None, Some input_pkt_hex, Some input_port ->
      Pass.{ cfg_checker;
             cfg_inputs = InputPktPort { input_pkt_hex;
                                         input_port; }; }
    | None, None, None ->
      failwith "Please supply the -stf or -pkt and -port flags."
    | None, Some _, None
    | None, None, Some _ ->
      failwith "Please specify both -pkt and -port."
    | Some _, Some _, None
    | Some _, None, Some _
    | Some _, Some _, Some _ ->
      failwith "The -stf flag cannot be used with -pkt or -port."
  ]

let cfg_command ~summary flags runner =
  let open Command.Let_syntax in
  Command.basic ~summary:summary
    [%map_open
      let cfg = flags in
      fun () ->
        runner cfg
        |> Petr4.Common.handle_error
        |> ignore]

let parser_command =
  cfg_command ~summary:"parse a P4 program" parser_flags Petr4.Unix.Driver.run_parser

let checker_command =
  cfg_command ~summary:"typecheck a P4 program" checker_flags Petr4.Unix.Driver.run_checker

let compiler_command =
  cfg_command ~summary:"compile a P4 program" compiler_flags Petr4.Unix.Driver.run_compiler

let interp_command =
  cfg_command ~summary:"run a P4 program" interp_flags Petr4.Unix.Driver.run_interpreter

let tbl_command =
  Command.basic ~summary:"EXPERIMENTAL: run table translation validation"
    (Command.Param.return
       (fun () -> Common.run_tbl ()))

let command =
  Command.group ~summary:"petr4: a reference implementation of the p4_16 language"
    ["parse", parser_command;
     "check", checker_command;
     "compile", compiler_command;
     "run", interp_command;
     "tbl", tbl_command]

let () =
  Command_unix.run ~version: "0.1.2" command

let () = ()
