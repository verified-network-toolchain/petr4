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

open Common
open Core_kernel
open Petr4
open Js_of_ocaml
open Js_of_ocaml_lwt

exception ParsingError of string

let preprocess _ p4_file_contents =
  let buf = Buffer.create 101 in
  let env = P4pp.Eval.{ file = "typed_input"; defines = []} in
  ignore (P4pp.Eval.preprocess_string [] env buf p4_file_contents);
  Buffer.contents buf

let eval_string verbose packet_string p4_file_contents =
  let pack = Cstruct.of_hex packet_string in
  match parse "input.p4" p4_file_contents verbose with
  | `Ok prog -> Eval.eval_program prog pack [] []
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
