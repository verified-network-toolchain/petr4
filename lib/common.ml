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
open Core
module P4info = P4P4info

module type DriverIO = sig
  val red: string -> string
  val green: string -> string
  val preprocess: Filename.t list -> Filename.t -> string
  val open_file: Filename.t -> Out_channel.t
  val close_file: Out_channel.t -> unit
end

type error =
  | PreprocessorError of exn
  | LexerError of string
  | ParserError of P4info.t
  | CheckerError of exn
  | GenLocError
  | NormalizeError of string
  | ToP4CubError of string
  | ToGCLError of string
  | FlattenDeclCtxError of string
  | ToCLightError of string
  (* not an error but an indicator to stop processing data *)
  | Finished

module MakeDriver (IO: DriverIO) = struct

  open Result

  let preprocess (cfg: Pass.parser_cfg) =
    try
      Ok (IO.preprocess cfg.cfg_includes cfg.cfg_infile)
    with ex -> Error (PreprocessorError ex)

  let lex (cfg: Pass.parser_cfg) (input: string) =
    try 
      let () = Lexer.reset () in
      let () = Lexer.set_filename cfg.cfg_infile in
      Ok (Lexing.from_string input)
    with Lexer.Error s -> Error (LexerError s)

  let parse cfg (lexbuf: Lexing.lexbuf) =
    try
      Ok (Parser.p4program Lexer.lexer lexbuf)
    with Parser.Error -> Error (ParserError (Lexer.info lexbuf))

  let print_surface (cfg: Pass.checker_cfg) (prog: Surface.program) =
    match cfg.cfg_p4surface with
    | Skip -> Error Finished
    | Run None -> Ok prog
    | Run (Some out) ->
      Format.eprintf "TODO: implement surface pretty printing.\n";
      Ok prog

  let check cfg (prog: Surface.program) =
    try
      let prog, renamer = Elaborate.elab prog in
      let _, typed_prog = Checker.check_program renamer prog in
      Ok typed_prog
    with e -> Error (CheckerError e)

  let gen_loc (cfg: Pass.checker_cfg) (prog: P4light.program) =
    match cfg.cfg_gen_loc with
    | Skip -> Ok prog
    | Run () ->
       match Poulet4.GenLoc.transform_prog P4info.dummy prog with
       | Coq_inl prog'' -> Ok prog''
       | Coq_inr ex     -> Error GenLocError

  let normalize (cfg: Pass.checker_cfg) (prog: P4light.program) =
    match cfg.cfg_normalize with
    | Skip -> Ok prog
    | Run () ->
       Ok (Poulet4.SimplExpr.transform_prog P4info.dummy prog)

  let print_p4light (cfg: Pass.checker_cfg) (prog: P4light.program) =
    match cfg.cfg_p4light with
    | Skip -> Error Finished
    | Run None -> Ok prog
    | Run (Some out) ->
      let oc = IO.open_file out.out_file in
      let fmt = Format.formatter_of_out_channel oc in
      begin match out.out_fmt with
        | Concrete ->
          Printp4.print_program
            fmt 
            ["core.p4"; "tna.p4";"common/headers.p4";"common/util.p4"] 
            ["@pragma pa_auto_init_metadata"]
            prog
        | Sexps ->
          Format.eprintf "TODO: implement p4light s-expression pretty printing.\n"
        | Coq ->
          Exportp4.print_program fmt prog
        | Ocaml ->
          Exportp4prune.print_program fmt prog
      end;
      IO.close_file oc;
      Ok prog

  let to_p4cub (cfg: Pass.compiler_cfg) (prog: P4light.program) =
    if Pass.is_skip cfg.cfg_p4cub
    then Error Finished
    else
      match Poulet4.ToP4cub.translate_program P4info.dummy prog with
      | Poulet4.Result.Ok cub  -> Ok cub
      | Poulet4.Result.Error e -> Error (ToP4CubError e)

  let print_p4cub (cfg: Pass.compiler_cfg) prog =
    match cfg.cfg_p4cub with
    | Skip -> Error Finished
    | Run None ->
       Ok prog
    | Run (Some out) ->
       let oc = IO.open_file out.out_file in
       let fmt = Format.formatter_of_out_channel oc in
       begin match out.out_fmt with
       | Concrete -> 
          Format.eprintf "TODO: implement p4cub concrete syntax pretty printing.\n"
       | Sexps ->
          Printp4cub.print_tp_decl fmt prog
       | Coq ->
          Format.eprintf "TODO: implement p4cub coq pretty printing.\n"
       | Ocaml ->
          Format.eprintf "TODO: implement p4cub OCaml pretty printing.\n"
       end;
       IO.close_file oc;
       Ok prog

  let to_p4flat (cfg: Pass.compiler_cfg) prog =
    match cfg.cfg_p4flat with
    | Skip -> Error Finished
    | Run p4flat_fmt ->
       Ok prog

  let print_p4flat (cfg: Pass.compiler_cfg) prog =
    match cfg.cfg_p4flat with
    | Skip -> Error Finished
    | Run None -> Ok prog
    | Run (Some p4flat_fmt) ->
       Format.eprintf "TODO: implement p4flat pretty printing.\n";
       Ok prog

  let to_gcl depth prog =
    let open Poulet4 in
    let gas = 100000 in
    let coq_gcl =
      V1model.gcl_from_p4cub P4info.dummy TableInstr.instr gas depth prog
    in
    begin match coq_gcl with
    | Result.Error msg -> Error (ToGCLError msg)
    | Result.Ok gcl    -> Ok gcl
    end

  let print_gcl (out: Pass.output) prog =
    Format.eprintf "TODO: implement GCL pretty printing.\n";
    Ok prog
  
  let flatten_declctx cub_ctx =
    match Poulet4.ToP4cub.flatten_DeclCtx cub_ctx with
    | Poulet4.Result.Ok cub  -> Ok cub
    | Poulet4.Result.Error e -> Error (FlattenDeclCtxError e)
  
  let hoist_clight_effects prog =
    Ok (Poulet4.Statementize.coq_TranslateProgram prog)

  let to_clight prog =
    let certd = Compcertalize.topdecl_convert prog in 
    match Poulet4_Ccomp.CCompSel.coq_Compile certd with
    | Poulet4_Ccomp.Errors.OK clight -> Ok clight
    | Poulet4_Ccomp.Errors.Error m ->
       match m with
       | Poulet4_Ccomp.Errors.MSG msg :: [] ->
          Error (ToCLightError (Base.String.of_char_list msg))
       | _ ->
          Error (ToCLightError ("Unknown failure in Ccomp"))
  
  let print_clight (out: Pass.output) prog =
    Format.eprintf "TODO: implement Clight pretty printing.\n";
    Ok prog

  let run_parser (cfg: Pass.parser_cfg) =
    preprocess cfg
    >>= lex cfg
    >>= parse cfg

  let run_checker (cfg: Pass.checker_cfg) =
    run_parser cfg.cfg_parser
    >>= print_surface cfg
    >>= check cfg
    >>= gen_loc cfg
    >>= normalize cfg
    >>= print_p4light cfg

  let run_compiler (cfg: Pass.compiler_cfg) =
    run_checker cfg.cfg_checker
    >>= to_p4cub cfg

    >>= to_p4flat cfg
    >>= print_p4flat cfg

    >>= begin fun prog ->
        match cfg.cfg_backend with
        | Skip -> Ok ()
        | Run (GCLBackend {depth; gcl_output}) ->
           to_gcl depth prog
           >>= print_gcl gcl_output
           >>= fun x -> Ok ()
        | Run (CBackend cfg_ccomp) ->
           flatten_declctx prog
           >>= hoist_clight_effects
           >>= print_p4cub cfg
           >>= to_clight
           >>= print_clight cfg_ccomp
           >>= fun x -> Ok ()
        end

  let run_interpreter (cfg: Pass.interpreter_cfg) =
    run_checker cfg.cfg_checker
    >>= fun p4prog ->
    match cfg.cfg_inputs with
    | InputSTF stf_filename ->
      let _ = Stf.run_stf stf_filename p4prog in
      Ok ()
    | InputPktPort { input_pkt_hex;
                     input_port } ->
      let _ = Stf.evaler p4prog input_pkt_hex input_port (fun _ -> None) in
      Ok ()

  let run (cfg: Pass.cmd_cfg) =
    let open Pass in
    match cfg with
    | CmdParse parse_cfg ->
      run_parser parse_cfg
      >>= fun _ -> Ok ()
    | CmdCheck check_cfg ->
      run_checker check_cfg
      >>= fun _ -> Ok ()
    | CmdCompile compile_cfg ->
      run_compiler compile_cfg
      >>= fun _ -> Ok ()
    | CmdInterp interp_cfg ->
      run_interpreter interp_cfg
      >>= fun _ -> Ok ()
end
