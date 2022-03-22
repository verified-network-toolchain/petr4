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

open Petr4
module P4Info = Info
open Core_kernel
module Info = P4Info
module Env = Prog.Env

let print pp = Format.printf "%a@." Pp.to_fmt pp

let fmt_print s = Format.printf "%s" s

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

  let do_stf include_dir stf_file p4_file =
    let print_err (e_port, e_pkt) (a_port, a_pkt) =
      Printf.printf "Packet differed from the expected packet.\nExpected: port %s pkt %s\nActual:   port %s pkt %s\n\n"
        e_port e_pkt a_port a_pkt
    in
    let print_ok (a_port, a_pkt) =
      Printf.printf "Packet matched the expected packet.\nPacket:   port %s pkt %s\n\n"
        a_port a_pkt
    in
    let check_pkt (expected_pkt, actual_pkt) =
      if not (P4stf.Test.packet_equal expected_pkt actual_pkt)
      then print_err expected_pkt actual_pkt
      else print_ok actual_pkt
    in
    let verbose = false in
    match parse_file include_dir p4_file verbose with
    | `Ok p4prog -> 
       let expected, results = P4stf.Test.run_stf stf_file p4prog in
       let pkts = List.zip_exn expected results in
       List.iter ~f:check_pkt pkts
    | `Error err -> 
       ()
       
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
      (pkt |> Cstruct.to_string |> Util.hex_of_string) ^ " port: " ^ Bigint.to_string port
    | `NoPacket -> "No packet out"
    | `Error(info, exn) ->
      let exn_msg = Exn.to_string exn in
      let info_string = Info.to_string info in
      info_string ^ "\n" ^ exn_msg

end
