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


open Petr4.Common
open Js_of_ocaml
open Js_of_ocaml_lwt

exception ParsingError of string

module Conf: Parse_config = struct
  let red s = s
  let green s = s

  let preprocess _ p4_file_contents =
    let buf = Buffer.create 101 in
    let file ="typed_input.p4" in
    let env = P4pp.Eval.{ file = file ; defines = []} in
    ignore (P4pp.Eval.preprocess_string [] env buf file p4_file_contents);
    Buffer.contents buf
end

module Parse = Make_parse(Conf)
open Parse

let eval verbose packet_str ctrl_str p4_contents =
  let ctrl_json = Yojson.Safe.from_string ctrl_str in
  eval_file [] p4_contents verbose packet_str ctrl_json

let () =
   let form_submit = Dom_html.getElementById "form-submit" in
   let text_area_of_string s  =
      match Dom_html.getElementById s |> Dom_html.CoerceTo.textarea |> Js.Opt.to_option with
      | Some x -> x
      | _ -> failwith "bad html"
    in
    let area_input = text_area_of_string "code-area" in
    let area_out = text_area_of_string "output" in
    let area_packet = text_area_of_string "packet-area" in
    let area_control_json = text_area_of_string "control-json-area" in
    Lwt.async @@ fun () ->
      Lwt_js_events.clicks form_submit @@ fun _ _ ->
        let packet = area_packet##.value |> Js.to_string in
        let control_json = area_control_json##.value |> Js.to_string in
        area_input##.value |> Js.to_string |> print_endline;
        let p4_content =
          area_input##.value
          |> Js.to_string
        in
        let out = eval true packet control_json p4_content |> Js.string in
        area_out##.value := out;
        Lwt.return ()
