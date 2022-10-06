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

module UnixIO : DriverIO = struct
  let colorize colors s = ANSITerminal.sprintf colors "%s" s
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

  let open_file path =
    Core_unix.open_process_out path

  let close_file ochan =
    match Core_unix.close_process_out ochan with
    | Ok () -> ()
    | Error _ -> failwith "Error in close_file"
  
end

module UnixDriver = MakeDriver(UnixIO)

let parse_ext_flag p =
  match p with
  | Some file ->
     Pass.Run (Some (Pass.parse_output_exn file))
  | None ->
     Pass.Run None

let parse_backend unroll_parsers output_gcl output_clight =
  match output_gcl, output_clight with
  | Some gcl, None ->
     begin match unroll_parsers with
     | Some depth ->
        let gcl_output = Pass.parse_output_exn gcl in
        Pass.Run (Pass.GCLBackend {depth; gcl_output})
     | None ->
        failwith "please provide a depth with -unroll-parsers when compiling to GCL"
     end
  | None, Some clight ->
     let clight_output = Pass.parse_output_exn clight in
     Pass.Run (Pass.CBackend clight_output)
  | Some _, Some _ ->
     failwith "Can produce either C or GCL but not both."
  | None, None ->
     Pass.Skip

let command =
  let open Command.Let_syntax in
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
        let p : Pass.compiler_cfg =
          {cfg_infile         = in_file;
           cfg_includes       = includes;
           cfg_verbose        = verbose;
           cfg_p4surface      = parse_ext_flag output_p4surface;
           cfg_gen_loc        = Pass.cfg_of_bool gen_loc;
           cfg_normalize      = Pass.cfg_of_bool normalize;
           cfg_p4light        = parse_ext_flag output_p4light;
           cfg_p4cub          = parse_ext_flag output_p4cub;
           cfg_p4flat         = parse_ext_flag output_p4flat;
           cfg_backend        = parse_backend
                                  unroll_parsers
                                  output_gcl
                                  output_c;
          }
        in
        match UnixDriver.run p with
        | Error Finished
        | Ok () -> ()
        | Error e -> failwith "TODO: printing for Common.error"]

let () = Command_unix.run ~version: "0.1.2" command
