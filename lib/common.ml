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
module P4P4info = P4info
open Core_kernel
module P4info = P4P4info

module type Parse_config = sig
  val red: string -> string
  val green: string -> string
  val preprocess: string list -> string -> string
end

(* This is a stand-in for Pretty.format_program *)
let pretty fmt p =
  Format.pp_print_string fmt "Sorry, I yanked the pretty-printer out while I was refactoring. Feel free to put it back - Ryan"

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
          Format.printf "%a@\n%!" pretty prog;
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
      (exportp4 : bool) (exportp4_ocaml: bool)(normalize : bool)
      (export_file : string) (gen_loc : bool) (verbose : bool) 
      (printp4 : bool) (printp4_file: string) : unit =
    match parse_file include_dirs p4_file verbose with
    | `Ok prog ->
      let prog, renamer = Elaborate.elab prog in
      let _, typed_prog = Checker.check_program renamer prog in
      Format.printf "%a" pretty prog;
      begin
        if exportp4 || exportp4_ocaml || printp4 then
          (* let oc = open_out ofile in *)
          (* let oc = Stdlib.open_out "out.v" in *)
          let prog' =
            if normalize then
              Poulet4.SimplExpr.transform_prog P4info.dummy typed_prog
            else typed_prog in
          let prog'' =
            if gen_loc then
              match Poulet4.GenLoc.transform_prog P4info.dummy prog' with
              | Coq_inl prog'' -> prog''
              | Coq_inr ex -> failwith "error occurred in GenLoc"
            else prog' in
          begin 
            if exportp4 then
            let oc = Out_channel.create export_file in
            Exportp4.print_program (Format.formatter_of_out_channel oc) prog'';
            Out_channel.close oc
          end;
          begin 
            if exportp4_ocaml then
            let oc = Out_channel.create export_file in
            Exportp4prune.print_program (Format.formatter_of_out_channel oc) prog'';
            Out_channel.close oc
          end;
          begin
            if printp4 then
            let oc_p4 = Out_channel.create printp4_file in
            Printp4.print_program (Format.formatter_of_out_channel oc_p4)
              ["core.p4"; "tna.p4";"common/headers.p4";"common/util.p4"] 
              ["@pragma pa_auto_init_metadata"]
              prog'';
            Out_channel.close oc_p4
          end;
      end
    | `Error (info, Lexer.Error s) ->
      Format.eprintf "%s: %s@\n%!" (P4info.to_string info) s
    | `Error (info, Parser.Error) ->
      Format.eprintf "%s: syntax error@\n%!" (P4info.to_string info)
    | `Error (info, err) ->
      Format.eprintf "%s: %s@\n%!" (P4info.to_string info) (Exn.to_string err)

 let compile_file (include_dirs : string list) (p4_file : string) 
      (normalize : bool)
      (export_file : string)  (verbose : bool) (gen_loc : bool) (print_p4cub: bool)
      (printp4_file: string) : unit =
    match parse_file include_dirs p4_file verbose with
    | `Ok prog ->
      let prog, renamer = Elaborate.elab prog in
      let _, typed_prog = Checker.check_program renamer prog in
          (* let oc = open_out ofile in *)
          (* let oc = Stdlib.open_out "out.v" in *)
          Poulet4_Ccomp.PrintClight.change_destination export_file;
          let prog' =
            if normalize then
              Poulet4.SimplExpr.transform_prog P4info.dummy typed_prog
            else typed_prog in
          let prog'' =
            if gen_loc then
              match Poulet4.GenLoc.transform_prog P4info.dummy prog' with
              | Coq_inl prog'' -> prog'' 
              | Coq_inr ex -> failwith "error occurred in GenLoc"
            else prog' in
          let prog''' = 
            match Poulet4.ToP4cub.translate_program' P4info.dummy prog'' with
            | Poulet4.Result.Result.Ok prog''' -> (prog'''|> Poulet4.Statementize.coq_TranslateProgram) 
            | Poulet4.Result.Result.Error e -> failwith e in
          if(print_p4cub) then (
              let oc_p4 = Out_channel.create printp4_file in
              Printp4cub.print_tp_decl (Format.formatter_of_out_channel oc_p4) prog''';
              Out_channel.close oc_p4);
          begin
           match (prog''' |> Compcertalize.topdecl_convert |> Poulet4_Ccomp.CCompSel.coq_Compile) with
           | Poulet4_Ccomp.Errors.Error (m) -> 
                let m' =
                 begin
                 match m with
                 | (Poulet4_Ccomp.Errors.MSG msg) ::[] -> Base.String.of_char_list msg
                 | _ -> "unknown failure from p4cub" 
                end in
              failwith m'
           | Poulet4_Ccomp.Errors.OK prog -> Poulet4_Ccomp.CCompSel.print_Clight prog
           end
    | `Error (info, Lexer.Error s) ->
      Format.eprintf "%s: %s@\n%!" (P4info.to_string info) s
    | `Error (info, Parser.Error) ->
      Format.eprintf "%s: syntax error@\n%!" (P4info.to_string info)
    | `Error (info, err) ->
      Format.eprintf "%s: %s@\n%!" (P4info.to_string info) (Exn.to_string err)

  

  let eval_file include_dirs p4_file verbose pkt_str ctrl_json port target =
    failwith "eval_file removed"
    (* TODO restore evaluator
    let port = Bigint.of_int port in
    let pkt = Cstruct.of_hex pkt_str in
    let open Yojson.Safe in
    let matches = ctrl_json
                  |> Util.member "matches"
                  |> Util.to_list
                  |> List.map ~f:Util.to_list in
    let vsets =
      List.map matches ~f:(fun l -> List.map l ~f:P4light.Match.of_yojson_exn) in
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
    | `Error (info, exn) as e-> e
    *)

  let eval_file_string include_dirs p4_file verbose pkt_str ctrl_json port target =
    failwith "eval_file_string removed"
    (* TODO restore evaluator
    match eval_file include_dirs p4_file verbose pkt_str ctrl_json port target with
    | `Ok (pkt, port) ->
      (pkt |> Cstruct.to_string |> hex_of_string) ^ " port: " ^ Bigint.to_string port
    | `NoPacket -> "No packet out"
    | `Error(info, exn) ->
      let exn_msg = Exn.to_string exn in
      let info_string = P4info.to_string info in
      info_string ^ "\n" ^ exn_msg
    *)

end
