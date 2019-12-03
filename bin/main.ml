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
(* open Core_extended.Std *)
open Petr4
open Common

exception ParsingError of string

let preprocess include_dirs p4file =
  let buf = Buffer.create 101 in
  let env = P4pp.Eval.{ file = p4file; defines = []} in
  ignore (P4pp.Eval.preprocess_file [] env buf p4file);
  Buffer.contents buf

let check_dir include_dirs p4_dir verbose =
  let dir_handle = Unix.opendir p4_dir in
  let rec loop () =
    match Unix.readdir_opt dir_handle with
    | None ->
      ()
    | Some file ->
      if Filename.check_suffix file "p4" then
        begin
          Printf.printf "Checking: %s\n" (Filename.concat p4_dir file);
          let p4_file = Filename.concat p4_dir file in
          match parse include_dirs p4_file verbose preprocess with
          | `Ok prog ->
             let prog = Elaborate.elab prog in
             Checker.check_program prog |> ignore;
             Printf.printf "OK:       %s\n" (Filename.concat p4_dir file);
          | `Error (info, Lexer.Error s) ->
             Format.eprintf "%s: %s@\n%!" (Info.to_string info) s
          | `Error (info, Petr4.Parser.Error) ->
             Format.eprintf "%s: syntax error@\n%!" (Info.to_string info)
          | `Error (info, err) ->
             Format.eprintf "%s: %s@\n%!" (Info.to_string info) (Exn.to_string err)
        end;
      loop () in
  loop ()

let command =
  let spec =
    let open Command.Spec in
    empty
    +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
    +> flag "-testdir" (optional string) ~doc:"<dir> Test all P4 files in directory"
    +> flag "-json" no_arg ~doc:"Emit parsed program as JSON on stdout"
    +> flag "-pretty" no_arg ~doc:"Pretty print JSON"
    +> flag "-verbose" no_arg ~doc:"Verbose mode"
    +> flag "-packet" (optional string) ~doc:"<file> Read a packet from file"
    +> flag "-ctrl" (optional string) ~doc:"<file> Read a control plane config from file"
    +> anon (maybe ("p4file" %:string)) in
  Command.basic_spec
    ~summary:"p4i: OCaml front-end for the P4 language"
    spec
    (fun include_dirs p4_dir print_json pretty_json verbose packet ctrl_file p4_file () ->
       match p4_dir, p4_file, packet, ctrl_file with
       | Some p4_dir,_,_,_ ->
         check_dir include_dirs p4_dir verbose
       | _, Some p4_file, Some pfile, Some cfile ->
         check_file include_dirs p4_file print_json pretty_json verbose preprocess;
          (* let packet_string =  *)
          let ctrl_json = Yojson.Safe.from_file cfile in
          let packet_string = Core_kernel.In_channel.read_all pfile in
          check_file include_dirs p4_file print_json pretty_json verbose preprocess;
          eval_file include_dirs packet_string ctrl_json verbose preprocess p4_file
          |> print_endline
       | _, _, _, _ -> ())

(*let () = check_file ["./examples"] "./examples/eval_tests/controls/table.p4" true true false*)

(*let () = eval_file ["./examples"] "./examples/eval_tests/parsers/value_set.p4" false "packets/sample_packet.txt" "./ctrl_configs/single_entry.json"
         |> print_endline*)

let () =
   Format.printf "@[";
   Command.run ~version:"0.1.1" command;
   Format.printf "@]"
