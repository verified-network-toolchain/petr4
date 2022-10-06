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
module UnixDriver =
  MakeDriver(struct
      let red s = colorize [ANSITerminal.red] s
      let green s = colorize [ANSITerminal.green] s
      
      let preprocess include_dirs p4file =
        let cmd =
          String.concat ~sep:" "
            (["cc"] @
               (List.map include_dirs ~f:(Printf.sprintf "-I%s") @
                  ["-undef"; "-nostdinc"; "-E"; "-x"; "c"; p4file])) in
        let in_chan = Core_unix.open_process_in cmd in
        let str = In_channel.input_all in_chan in
        let _ = Core_unix.close_process_in in_chan in
        str
      
    end)

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
     +> flag "-port" (optional_with_default "0" string) ~doc: "<port_number> Specify ingress port"
     +> flag "-T" (optional_with_default "v1" string) ~doc: "<target> Specify P4 target (v1, ebpf currently supported)"
     +> anon ("p4file" %: string))
    (fun verbose include_dir pkt_str port target p4file () ->
       print_string (eval_file_string include_dir p4file verbose pkt_str (int_of_string port) target))

let compile_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Compile a P4 program to C"
     (empty
     +> flag "-v" no_arg ~doc:" Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> flag "-normalize" no_arg ~doc:" Simplify expressions in P4"
     +> flag "-export-file" (optional_with_default "compiled.c" string) ~doc:"Path to export compiled c file"
     +> flag "-gen-loc" no_arg ~doc:" Generate locators in AST"
     +> flag "-printp4cub" no_arg ~doc: "Print the p4cub AST"
     +> flag "-printp4-file" (optional_with_default "cubast.txt" string)~doc:"Path to print the p4cub syntax"
     +> flag "-gcl" (listed int)  ~doc:"G,P Compile to GCL using G to unroll the inliner and P to unroll the parser" 
     +> anon ("p4file" %: string))
    (fun verbose include_dir normalize export_file gen_loc printp4cub printp4_file gcl p4file () ->
       ignore (compile_file include_dir p4file normalize export_file verbose gen_loc printp4cub printp4_file gcl))

let do_stf _ _ _ = failwith "do_stf unimplemented"

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

let cli_command =
  let open Command.Let_syntax in
  let open Command.Param in
  Command.basic ~summary:"TODO better summary here please"
    [%map_open
     let verbose = flag "-v" no_arg
                     ~doc:"Be more verbose."
     and includes = flag "-I" (listed string)
                      ~doc:"Paths to search for files sourced with #include directives."
     and normalize = flag "-normalize" no_arg
                       ~doc:"Simplify expressions."
     and gen_loc = flag "-gen-loc" no_arg
                     ~doc:"Infer locators in P4light AST after typechecking."
     and unroll_parsers = flag "-unroll-parsers" (optional int)
                            ~doc:"Unroll parsers to given depth."
     and output_p4surface = flag "-output-p4surface" (optional string)
                           ~doc:"Output P4surface AST to the specified file."
     and output_p4light = flag "-output-p4light" (optional string)
                           ~doc:"Output P4light to the specified file."
     and output_p4cub = flag "-output-p4cub" (optional string)
                           ~doc:"Output P4Cub to the specified file."
     and output_p4flat = flag "-output-p4flat" (optional string)
                           ~doc:"Output P4flat to the specified file."
     and output_gcl = flag "-output-gcl" (optional string)
                           ~doc:"Output GCL to the specified file."
     and output_c = flag "-output-c" (optional string)
                           ~doc:"Output C to the specified file."
     and in_file = anon ("file.p4" %: string)
     in fun () ->
        let parse_ext_flag p =
          match p with
          | Some file ->
             begin match Pass.parse_output file with
             | Some f -> Pass.Run (Some f)
             | None -> failwith ("bad extension " ^ file)
             end
          | None ->
             Pass.Run None in
        let parse_unroll u =
          match u with
          | Some depth -> Pass.Run depth
          | None       -> Pass.Skip in
        let p : Pass.compiler_cfg =
          {cfg_infile         = in_file;
           cfg_includes       = includes;
           cfg_verbose        = verbose;
           cfg_p4surface      = parse_ext_flag output_p4surface;
           cfg_gen_loc        = Pass.cfg_of_bool gen_loc;
           cfg_normalize      = Pass.cfg_of_bool normalize;
           cfg_p4light        = parse_ext_flag output_p4light;
           cfg_p4cub          = parse_ext_flag output_p4cub;
           cfg_unroll_parsers = parse_unroll unroll_parsers;
           cfg_p4flat         = parse_ext_flag output_p4flat;
           cfg_gcl            = parse_ext_flag output_gcl;
          }
        in
        run_compiler p]

let command =
  Command.group
    ~summary: "Petr4: A reference implementation of the P4_16 language"
    [ "parse", parse_command;
      "typecheck", check_command;
      "compile", compile_command;
      "run", eval_command;
      "stf", stf_command ]

let () = Command_unix.run ~version: "0.1.2" command
