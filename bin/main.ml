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
open Core_extended.Std
open Petr4

exception ParsingError of string

let colorize colors s = Console.Ansi.string_with_attr colors s
let red s = colorize [`Red] s
let green s = colorize [`Green] s

let preprocess include_dirs p4file =
  Core_extended.Shell.run_full "cc"
    (List.map include_dirs ~f:(Printf.sprintf "-I%s") @
     ["-undef"; "-nostdinc"; "-E"; "-x"; "c"; p4file])

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

let check_file include_dirs p4_file print_json pretty_json verbose =
  match parse include_dirs p4_file verbose with
  | `Ok prog ->
    let _ = Checker.check_program prog in
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

let eval_file include_dirs p4_file verbose =
  match parse include_dirs p4_file verbose with
  | `Ok prog -> Eval.eval_program prog
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
    +> anon (maybe ("p4file" %:string)) in
  Command.basic_spec
    ~summary:"p4i: OCaml front-end for the P4 language"
    spec
    (fun include_dirs p4_dir print_json pretty_json verbose p4_file () ->
       match p4_dir, p4_file with
       | Some p4_dir,_ ->
         check_dir include_dirs p4_dir verbose
       | _, Some p4_file ->
         (* check_file include_dirs p4_file print_json pretty_json verbose; *)
         let _ = eval_file include_dirs p4_file verbose in ()
       | None, None -> ())

let () = eval_file ["./examples"] "examples/eval_tests/expressions/equality.p4" false

(* let () =
  Format.printf "@[";
  Command.run ~version:"0.1.1" command;
  Format.printf "@]" *)
