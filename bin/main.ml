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
          match parse_file include_dirs p4_file verbose with
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

let check_command =
  let open Command.Spec in
  Command.basic_spec
    ~summary: "Check syntax of P4_16 file"
    (empty
     +> flag "-v" no_arg ~doc:" Enable verbose output"
     +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
     +> flag "-json" no_arg ~doc:" Print parsed tree as JSON"
     +> flag "-pretty" no_arg ~doc:" Pretty-print JSON"
     +> anon ("p4file" %: string))
     (fun verbose include_dir json pretty p4file () ->
       ignore (check_file include_dir p4file json pretty verbose))

let command =
  Command.group
    ~summary: "Petr4: A reference implementation of the P4_16 language"
    ["check", check_command]

let () = Command.run ~version: "0.1.1" command
