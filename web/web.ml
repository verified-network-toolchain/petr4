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

exception ParsingError of string

let hash = Hashtbl.create(module String)
let input_name = "input.p4"

module HashFS = struct
  let exists path =
    match Hashtbl.find hash path with
      | Some _ -> true
      | None -> false

  let load path = Hashtbl.find_exn hash path
end

module Pp = P4pp.Eval.Make(HashFS)

module WebIO : DriverIO = struct
  let red s = s
  let green s = s

  let preprocess _ p4_file_contents =
    let env = P4pp.Eval.empty input_name ["/include"] [] in
    let str, _ = Pp.preprocess env input_name p4_file_contents in
    str

  let open_file f = failwith "unimplemented"
  let close_file f = failwith "unimplemented"
end

module WebDriver = MakeDriver(WebIO)

let eval verbose packet_str add ctrl_str p4_contents =
  failwith "eval unimplemented"

let _ =
  Js.export "Petr4"
    (object%js
       method eval packet control_string p4_content =
        try
          eval true (Js.to_string packet) [] (Js.to_string control_string) (Js.to_string p4_content) |> Js.string
        with e ->
          Exn.to_string e |> Js.string
     end)
