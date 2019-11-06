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

open Core_kernel
open Petr4
open Js_of_ocaml
open Js_of_ocaml_lwt

exception ParsingError of string

let preprocess p4_file_contents =
  let buf = Buffer.create 101 in
  let env = P4pp.Eval.{ file = "typed_input"; defines = []} in
  ignore (P4pp.Eval.preprocess_string [] env buf p4_file_contents);
  Buffer.contents buf

(*cc needs to be called before this, requiring this from users for now*)
let parse p4_file_name (p4_file_contents:string) verbose =
  let () = Lexer.reset () in
  let () = Lexer.set_filename p4_file_name in
  let lexbuf = Lexing.from_string p4_file_contents in
  try
    let prog = Parser.p4program Lexer.lexer lexbuf in
    if verbose then Format.eprintf "[%s] %s@\n%!" ("Passed") p4_file_name;
    `Ok prog
  with
  | err ->
    if verbose then Format.eprintf "[%s] %s@\n%!" ("Failed") p4_file_name;
    Lexer.info lexbuf |> Petr4.Info.to_string |> print_endline;
    `Error (Lexer.info lexbuf, err)

let check_file (p4_file_name : string) (p4_file_contents : string)
    (print_json : bool) (pretty_json : bool) (verbose : bool) : unit =
  match parse p4_file_name p4_file_contents verbose with
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

let eval_file p4_file_name verbose pfile =
  let packet_string = Core_kernel.In_channel.read_all pfile in
  let pack = Cstruct.of_hex packet_string in
  let p4_file_contents = Core_kernel.In_channel.read_all p4_file_name in
  match parse p4_file_name p4_file_contents verbose with
  | `Ok prog -> Eval.eval_program prog pack []
  | _ -> failwith "error unhandled"

let eval_string verbose packet_string p4_file_contents =
  let pack = Cstruct.of_hex packet_string in
  match parse "input.p4" p4_file_contents verbose with
  | `Ok prog -> Eval.eval_program prog pack []
  | _ -> "error when evaluating program!"


let () =
   let form_submit = Dom_html.getElementById "form-submit" in
   let text_area_of_string s  =
      match Dom_html.getElementById s |> Dom_html.CoerceTo.textarea |> Js.Opt.to_option with
      | Some x -> x
      | _ -> failwith "unimp"
    in
    let area_input = text_area_of_string "code-area" in
    let area_out = text_area_of_string "output" in
    let area_packet = text_area_of_string "packet-area" in
    Lwt.async @@ fun () ->
      Lwt_js_events.clicks form_submit @@ fun _ _ ->
        let packet = area_packet##.value |> Js.to_string in
        area_input##.value |> Js.to_string |> print_endline;
        area_out##.value :=
          area_input##.value
          |> Js.to_string
          |> preprocess
          |> eval_string true packet
          |> Js.string;
        Lwt.return ()
