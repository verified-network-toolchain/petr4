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

let preprocess _ p4_file_contents =
  let buf = Buffer.create 101 in
  let file ="typed_input.p4" in
  let env = P4pp.Eval.{ file = file ; defines = []} in
  ignore (P4pp.Eval.preprocess_string [] env buf file p4_file_contents);
  Buffer.contents buf

let eval_string verbose packet_string ctrl_string p4_file_contents =
  let ctrl_json = Yojson.Safe.from_string ctrl_string in
  eval_file [] packet_string ctrl_json verbose preprocess p4_file_contents

let control_json_string =
{|{
  "pre_entries": [
    {
      "annotations": [],
      "matches": [
        [
          [
            "info",
            {
              "filename": "./examples/eval_tests/controls/table.p4\"",
              "line_start": 44,
              "line_end": null,
              "col_start": 12,
              "col_end": 15
            }
          ],
          [
            "Expression",
            {
              "expr": [
                [
                  "info",
                  {
                    "filename": "./examples/eval_tests/controls/table.p4\"",
                    "line_start": 44,
                    "line_end": null,
                    "col_start": 12,
                    "col_end": 15
                  }
                ],
                [
                  "int",
                  [
                    [
                      "info",
                      {
                        "filename": "./examples/eval_tests/controls/table.p4\"",
                        "line_start": 44,
                        "line_end": null,
                        "col_start": 12,
                        "col_end": 15
                      }
                    ],
                    {
                      "value": 0,
                      "width_signed": [
                        9,
                        false
                      ]
                    }
                  ]
                ]
              ]
            }
          ]
        ]
      ],
      "action": [
        [
          "info",
          {
            "filename": "./examples/eval_tests/controls/table.p4\"",
            "line_start": 44,
            "line_end": null,
            "col_start": 18,
            "col_end": 25
          }
        ],
        {
          "annotations": [],
          "name": [
            [
              "info",
              {
                "filename": "./examples/eval_tests/controls/table.p4\"",
                "line_start": 44,
                "line_end": null,
                "col_start": 18,
                "col_end": 25
              }
            ],
            "set_one"
          ],
          "args": []
        }
      ]
    }
  ],
  "matches": [
      [
        [
          [
            "info",
            {
              "filename": "./examples/eval_tests/parsers/value_set.p4\"",
              "line_start": 23,
              "line_end": null,
              "col_start": 12,
              "col_end": 14
            }
          ],
          [
            "Expression",
            {
              "expr": [
                [
                  "info",
                  {
                    "filename": "./examples/eval_tests/parsers/value_set.p4\"",
                    "line_start": 23,
                    "line_end": null,
                    "col_start": 12,
                    "col_end": 14
                  }
                ],
                [
                  "int",
                  [
                    [
                      "info",
                      {
                        "filename":
                          "./examples/eval_tests/parsers/value_set.p4\"",
                        "line_start": 23,
                        "line_end": null,
                        "col_start": 12,
                        "col_end": 14
                      }
                    ],
                    { "value": 42, "width_signed": null }
                  ]
                ]
              ]
            }
          ]
        ]
      ]
    ]
}|}

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
          |> eval_string true packet control_json_string
          |> Js.string;
        Lwt.return ()
