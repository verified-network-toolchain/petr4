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
open Base
open Pack


exception ParsingError of string



module Pythonfs = struct
  let exists path = 
    let ld= AssocListMap.find path pack in
    match ld with
    |None->false
    |Some x-> true

  let load (path: string) : string =
    let ld= AssocListMap.find path pack in
    match ld with
    |None->""
    |Some x-> x
end

module Pp = P4pp.Eval.Make(Pythonfs)

module Conf: Parse_config = struct
  let red s = s
  let green s = s

  let preprocess _ p4_file_contents =
    let file ="input.p4" in
    let env = P4pp.Eval.empty file ["/include"] [] in
    let str,_ = Pp.preprocess env file p4_file_contents in
    str
end

module Parse = Make_parse(Conf)
open Parse

let eval verbose packet_str add ctrl_str p4_contents =
  let ctrl_json = Yojson.Safe.from_string ctrl_str in
  eval_file_string [] p4_contents verbose packet_str ctrl_json 0 "v1"
(* stp: the return type of this function has changed; not sure if that breaks anything *)
let _ =
  Js.export "Petr4"
    (object%js
      method load path =
        Pythonfs.load(Js.to_string path) |> Js.string
      method eval packet control_string p4_content =
        try
          eval false (Js.to_string packet) [] (Js.to_string control_string) (Js.to_string p4_content) |> Js.string
        with e ->
          Exn.to_string e |> Js.string
    end)
