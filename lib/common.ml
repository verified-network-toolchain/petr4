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

let fprint (chan: Out_channel.t) (pp: 'a Pp.t) =
  Format.fprintf (Format.formatter_of_out_channel chan) "%a@." Pp.to_fmt pp

let print (pp: 'a Pp.t) =
  fprint stdout pp

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
          prog |> Pretty.format_program |> print;
          Format.print_string "@\n%!"; 
          Format.printf "----------@\n";
          Format.printf "%s@\n%!" (prog |> Types.program_to_yojson |> Yojson.Safe.pretty_to_string)
        end;
      `Ok prog
    with
    | err ->
      if verbose then Format.eprintf "[%s] %s@\n%!" (Conf.red "Failed") p4_file;
      `Error (Lexer.info lexbuf, err)

  let parse_string p4_string = 
    let () = Lexer.reset () in
    let () = Lexer.set_filename p4_string in
    let lexbuf = Lexing.from_string p4_string in
    Parser.p4program Lexer.lexer lexbuf 

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

  let check_file' (include_dirs : string list) (p4_file : string) (verbose : bool) =
    match parse_file include_dirs p4_file verbose with
    | `Ok prog ->
      let prog, renamer = Elaborate.elab prog in
      `Ok (prog, Checker.check_program renamer prog)
    | `Error e -> `Error e

  let print_json (pretty: bool) (json: Yojson.Safe.t) : unit =
    let s =
      if pretty
      then Yojson.Safe.pretty_to_string json
      else Yojson.Safe.to_string json
    in
    Format.printf "%s" s

  let check_file (include_dirs : string list) (p4_file : string)
      (show_json : bool) (pretty_json : bool) (verbose : bool) : unit =
    match check_file' include_dirs p4_file verbose with
    | `Ok (parsed_prog, _) ->
      if show_json
      then parsed_prog |> Types.program_to_yojson |> print_json pretty_json
      else parsed_prog |> Pretty.format_program |> print
    | `Error (info, Lexer.Error s) ->
      Format.eprintf "%s: %s@\n%!" (Info.to_string info) s
    | `Error (info, Parser.Error) ->
      Format.eprintf "%s: syntax error@\n%!" (Info.to_string info)
    | `Error (info, err) ->
      Format.eprintf "%s: %s@\n%!" (Info.to_string info) (Exn.to_string err)

  let eval_file include_dirs p4_file verbose pkt_str ctrl_json port target =
    let port = Bigint.of_int port in
    let pkt = Cstruct.of_hex pkt_str in
    let open Yojson.Safe in
    let matches = ctrl_json
                  |> Util.member "matches"
                  |> Util.to_list
                  |> List.map ~f:Util.to_list in
    let vsets =
      List.map matches ~f:(fun l -> List.map l ~f:Prog.Match.of_yojson_exn) in
    match parse_file include_dirs p4_file verbose with
    | `Ok prog ->
      let elab_prog, renamer = Elaborate.elab prog in
      let (cenv, typed_prog) = Checker.check_program renamer elab_prog in
      let env = Env.CheckerEnv.eval_env_of_t cenv in
      let open Eval in
      begin match target with
        | "v1" ->
          let st = V1Interpreter.empty_state in
          begin match V1Interpreter.eval_program (([],[]), vsets) env st pkt port typed_prog |> snd with
            | Some (pkt,port) -> `Ok(pkt, port)
            | None -> `NoPacket
          end
        | "ebpf" ->
          let st = EbpfInterpreter.empty_state in
          begin match EbpfInterpreter.eval_program (([],[]), vsets) env st pkt port typed_prog |> snd with
            | Some (pkt, port) -> `Ok(pkt,port)
            | None -> `NoPacket
          end
        | _ -> Format.sprintf "Architecture %s unsupported" target |> failwith
      end
    | `Error (info, exn) as e -> e

  let eval_file_string include_dirs p4_file verbose pkt_str ctrl_json port target =
    match eval_file include_dirs p4_file verbose pkt_str ctrl_json port target with
    | `Ok (pkt, port) ->
      (pkt |> Cstruct.to_string |> hex_of_string) ^ " port: " ^ Bigint.to_string port
    | `NoPacket -> "No packet out"
    | `Error(info, exn) ->
      let exn_msg = Exn.to_string exn in
      let info_string = Info.to_string info in
      info_string ^ "\n" ^ exn_msg

  let ccomp_file verbose include_dirs p4_file =
    match check_file' include_dirs p4_file verbose with
    | `Ok (parsed_prog, (checker_env, checked_prog)) ->
      print_endline("type check passed");
      checked_prog
      |> Ccomp.compile
      |> Cprinter.format_cprog
    | `Error (info, err) ->
      print_endline("type check failed");
      let exn_msg = Exn.to_string err in
      let info_string = Info.to_string info in
      info_string ^ "\n" ^ exn_msg |> Pp.text
end
