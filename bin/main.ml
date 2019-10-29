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

exception ParsingError of string

let colorize colors s = ANSITerminal.sprintf colors "%s" s
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

let parse include_dirs p4_file verbose =
  let () = Lexer.reset () in
  let () = Lexer.set_filename p4_file in
  let p4_string = preprocess include_dirs p4_file in
  let lexbuf = Lexing.from_string p4_string in
  try
    let prog = Parser.p4program Lexer.lexer lexbuf in
    if verbose then Format.eprintf "[%s] %s@\n%!" (green "Passed") p4_file;
    `Ok prog
  with
  | err ->
    if verbose then Format.eprintf "[%s] %s@\n%!" (red "Failed") p4_file;
    `Error (Lexer.info lexbuf, err)

let check_file (include_dirs : string list) (p4_file : string)
    (print_json : bool) (pretty_json : bool) (verbose : bool) : unit =
  match parse include_dirs p4_file verbose with
  | `Ok prog ->
    let _ = () (*Checker.check_program prog*) in
    if print_json then
      let json = Types.program_to_yojson prog in
      let to_string j =
        if pretty_json then
          Yojson.Safe.pretty_to_string j
        else
          Yojson.Safe.to_string j in
      Format.printf "%s" (to_string json)
    else
      Format.printf "%a" Pretty.format_program prog
  | `Error (info, Lexer.Error s) ->
    Format.eprintf "%s: %s@\n%!" (Info.to_string info) s
  | `Error (info, Parser.Error) ->
    Format.eprintf "%s: syntax error@\n%!" (Info.to_string info)
  | `Error (info, err) ->
    Format.eprintf "%s: %s@\n%!" (Info.to_string info) (Exn.to_string err)


let eval_file include_dirs p4_file verbose pfile cfile =
  let packet_string = Core_kernel.In_channel.read_all pfile in
  let pack = Cstruct.of_hex packet_string in
  let open Yojson.Safe in
  let ctrl_json = from_file cfile in
  let pre_entries = ctrl_json |> Util.member "pre_entries" |> Util.to_list in
  let ctrl = List.map pre_entries ~f:Types.Table.pre_entry_of_yojson_exn in
  match parse include_dirs p4_file verbose with
  | `Ok prog -> Eval.eval_program prog pack ctrl
  | _ -> failwith "error unhandled"

let check_dir include_dirs p4_dir verbose =
  let dir_handle = Unix.opendir p4_dir in
  let rec loop () =
    match Unix.readdir_opt dir_handle with
    | None ->
      ()
    | Some file ->
      if Filename.check_suffix file "p4" then
        begin
          let p4_file = Filename.concat p4_dir file in
          match parse include_dirs p4_file verbose with
          | `Ok _ -> ()
          | `Error (info, Lexer.Error s) ->
            Format.eprintf "%s: %s@\n%!" (Info.to_string info) s
          | `Error (info, Parser.Error) ->
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
    (fun include_dirs p4_dir print_json pretty_json verbose packet p4_file ctrl_file () ->
       match p4_dir, p4_file, packet, ctrl_file with
       | Some p4_dir,_,_,_ ->
         check_dir include_dirs p4_dir verbose
       | _, Some p4_file, Some pfile, Some cfile ->
         check_file include_dirs p4_file print_json pretty_json verbose;
         let _ = eval_file include_dirs p4_file verbose pfile cfile in ()
       | _, _, _, _ -> ())

(*let () = check_file ["./examples"] "./examples/eval_tests/controls/table.p4" true true false*)

let () = eval_file ["./examples"] "./examples/eval_tests/controls/table2.p4" false "packets/sample_packet.txt" "./ctrl_configs/single_entry.json"

(* let () =
   Format.printf "@[";
   Command.run ~version:"0.1.1" command;
   Format.printf "@]" *)
