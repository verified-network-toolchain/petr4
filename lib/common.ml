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

module P4Info = Info
open Core_kernel
module Info = P4Info

module type Parse_config = sig
  val red: string -> string
  val green: string -> string
  val preprocess: string list -> string -> string
end

module Make_parse (Conf: Parse_config) = struct
  let parse_file include_dirs p4_file verbose =
    let () = Lexer.reset () in
    let () = Lexer.set_filename p4_file in
    let p4_string = Conf.preprocess include_dirs p4_file in
    let lexbuf = Lexing.from_string p4_string in
    try
      let prog = Parser.p4program Lexer.lexer lexbuf in
      if verbose then Format.eprintf "[%s] %s@\n%!" (Conf.green "Passed") p4_file;
      `Ok prog
    with
    | err ->
      if verbose then Format.eprintf "[%s] %s@\n%!" (Conf.red "Failed") p4_file;
      `Error (Lexer.info lexbuf, err)

  let check_file (include_dirs : string list) (p4_file : string) 
      (print_json : bool) (pretty_json : bool) (verbose : bool) : unit =
    match parse_file include_dirs p4_file verbose with
    | `Ok prog ->
      let prog = Elaborate.elab prog in
      Checker.check_program prog |> ignore;
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

    let eval_file include_dirs p4_file verbose pkt_str ctrl_json =
      (* let pkt_str = Core_kernel.In_channel.read_all pkt_file in *)
      let pkt = Cstruct.of_hex pkt_str in
      let open Yojson.Safe in
      let pre_entries = ctrl_json
                        |> Util.member "pre_entries"
                        |> Util.to_list in
      let tbls = List.map pre_entries ~f:Types.Table.pre_entry_of_yojson_exn in
      let matches = ctrl_json
                    |> Util.member "matches"
                    |> Util.to_list
                    |> List.map ~f:Util.to_list in
      let vsets =
        List.map matches ~f:(fun l -> List.map l ~f:Types.Match.of_yojson_exn) in
      match parse_file include_dirs p4_file verbose with
      | `Ok prog -> Eval.eval_program prog (tbls, vsets) pkt
      | `Error (info, exn) ->
        let exn_msg = Exn.to_string exn in
        let info_string = Info.to_string info in
        info_string ^ "\n" ^ exn_msg
end
