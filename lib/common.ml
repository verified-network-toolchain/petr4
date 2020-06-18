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
module Env = Prog.Env

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
      if verbose then
        begin
          Format.eprintf "[%s] %s@\n%!" (Conf.green "Passed") p4_file;
          Format.printf "%a@\n%!" Pretty.format_program prog;
          Format.printf "----------@\n";
          Format.printf "%s@\n%!" (prog |> Types.program_to_yojson |> Yojson.Safe.pretty_to_string)
        end;
      `Ok prog

    with
    | err ->
      if verbose then Format.eprintf "[%s] %s@\n%!" (Conf.red "Failed") p4_file;
      `Error (Lexer.info lexbuf, err)

  let hex_of_nibble (i : int) : string =
    match i with
    | 0 -> "0"
    | 1 -> "1"
    | 2 -> "2"
    | 3 -> "3"
    | 4 -> "4"
    | 5 -> "5"
    | 6 -> "6"
    | 7 -> "7"
    | 8 -> "8"
    | 9 -> "9"
    | 10 -> "A"
    | 11 -> "B"
    | 12 -> "C"
    | 13 -> "D"
    | 14 -> "E"
    | 15 -> "F"
    | _ -> failwith "unreachable"

  let hex_of_int (i : int) : string =
    hex_of_nibble (i/16) ^ hex_of_nibble (i%16) ^ " "

  let hex_of_char (c : char) : string =
    c |> Char.to_int |> hex_of_int

  let hex_of_string (s : string) : string =
    s
    |> String.to_list
    |> List.map ~f:hex_of_char
    |> List.fold_left ~init:"" ~f:(^)

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

  let eval_file include_dirs p4_file verbose pkt_str ctrl_json st port =
    (* let pkt_str = Core_kernel.In_channel.read_all pkt_file in *)
    let st = match st with None -> Eval.V1Interpreter.empty_state | Some st -> st in
    let port = Bigint.of_int port in
    let pkt = Cstruct.of_hex pkt_str in
    let open Yojson.Safe in
    let pre_entries = ctrl_json
                      |> Util.member "pre_entries"
                      |> Util.to_list in
    let tbls = List.map pre_entries ~f:Prog.Table.pre_entry_of_yojson_exn in
    let matches = ctrl_json
                  |> Util.member "matches"
                  |> Util.to_list
                  |> List.map ~f:Util.to_list in
    let vsets =
      List.map matches ~f:(fun l -> List.map l ~f:Prog.Match.of_yojson_exn) in
    match parse_file include_dirs p4_file verbose with
    | `Ok prog ->
      let elab_prog = Elaborate.elab prog in
      let (cenv, typed_prog) = Checker.check_program elab_prog in
      let env = Env.CheckerEnv.eval_env_of_t cenv in
      (* TODO - thread env information from checker to eval*)
      let open Eval in
      begin match V1Interpreter.eval_prog (tbls, vsets) env st pkt port typed_prog with
        | st, Some (pkt,port) -> st, `Ok(pkt, port)
        | st, None -> st, `NoPacket end
    | `Error (info, exn) as e-> st, e

  let eval_file_string include_dirs p4_file verbose pkt_str ctrl_json st port =
    match eval_file include_dirs p4_file verbose pkt_str ctrl_json st port with
    | _, `Ok (pkt, port) ->
      (pkt |> Cstruct.to_string |> hex_of_string) ^ " port: " ^ Bigint.to_string port
    | _, `NoPacket -> "No packet out"
    | _, `Error(info, exn) ->
      let exn_msg = Exn.to_string exn in
      let info_string = Info.to_string info in
      info_string ^ "\n" ^ exn_msg
end
