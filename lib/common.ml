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
  | ToP4CubError of string
  | ToP4flatError of string
  | TableOptError of string
  | ToGCLError of string
  | ToCLightError of string
  (* not an error but an indicator to stop processing data *)
  | Finished

let error_to_string (e : error) : string =
  match e with
  | PreprocessorError pp ->
    Printf.sprintf "preprocessor error: %s" (Exn.to_string pp)
  | LexerError s ->
    Printf.sprintf "lexer error: %s" s
  | ParserError info ->
    Printf.sprintf "parser error: %s" (P4info.to_string info)
  | CheckerError exn ->
    Printf.sprintf "checker error: %s" (Exn.to_string exn)
  | GenLocError ->
    Printf.sprintf "genloc error: TODO add debug message"
  | ToP4CubError s ->
    Printf.sprintf "top4cub error: %s" s
  | ToP4flatError s ->
    Printf.sprintf "top4flat error: %s" s
  | TableOptError s ->
    Printf.sprintf "table_opt error: %s" s
  | ToGCLError s ->
    Printf.sprintf "togcl error: %s" s
  | ToCLightError s ->
    Printf.sprintf "toclight error: %s" s
  | Finished ->
    Printf.sprintf "error [Finished] (not actually an error)"

let handle_error (res : ('a, error) Result.t) : 'a =
  match res with
  | Ok a -> a
  | Error e ->
    failwith (error_to_string e)

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
      Ok (P4parser.p4program Lexer.lexer lexbuf)
    with P4parser.Error -> Error (ParserError (Lexer.info lexbuf))

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
       | Sexps -> P4cubSexp.print fmt prog
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
      match Poulet4.P4cubToP4flat.translate_prog prog with
      | Poulet4.Result.Ok flat -> Ok flat
      | Poulet4.Result.Error e -> Error (ToP4flatError e)

  let write_p4cub_to_file prog printp4_file =
    let oc_p4 = Out_channel.create printp4_file in
    Printp4cub.print_prog (Format.formatter_of_out_channel oc_p4) prog;
    Out_channel.close oc_p4

  let print_p4flat (cfg: Pass.compiler_cfg) prog =
    match cfg.cfg_p4flat with
    | Skip -> Error Finished
    | Run None -> Ok prog
    | Run (Some p4flat_fmt) ->
       Format.eprintf "TODO: implement p4flat pretty printing.\n";
       Ok prog

  let table_opt (cfg: Pass.compiler_cfg) prog =
    match Poulet4.TLang.optimize_p4flat (fun x -> x) prog with
      | Poulet4.Result.Ok prog -> Ok prog
      | Poulet4.Result.Error e -> Error (TableOptError e)

  let to_gcl depth prog =
    let open Poulet4 in
    let gas = 100000 in
    let coq_gcl =
      V1model.gcl_from_p4cub TableInstr.instr true gas depth prog
    in
    begin match coq_gcl with
    | Result.Error msg -> Error (ToGCLError msg)
    | Result.Ok gcl    -> Ok gcl
    end

  let print_gcl (out: Pass.output) prog =
    Format.eprintf "TODO: implement GCL pretty printing.\n";
    Ok prog
  
  let flatten_declctx cub_ctx =
    Ok (Poulet4.ToP4cub.flatten_DeclCtx cub_ctx)
  
  let hoist_clight_effects prog =
    Ok (Poulet4.Statementize.lift_program prog)

  let to_clight prog =
    let certd = List.map ~f:Compcertalize.topdecl_convert prog in
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
    (* normalize must come before gen_loc *)
    >>= normalize cfg
    >>= gen_loc cfg
    >>= print_p4light cfg

  let run_compiler (cfg: Pass.compiler_cfg) =
    run_checker cfg.cfg_checker
    >>= to_p4cub cfg
    >>= begin fun prog ->
        match cfg.cfg_backend with
        | Skip -> Ok ()
        | Run TblBackend ->
          flatten_declctx prog
          >>= to_p4flat cfg
          >>= table_opt cfg
          >>= fun x -> Ok ()
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

let print_fun (f: Poulet4.P4flatToGCL.p4funs) : string =
  let open Poulet4.P4flatToGCL in
  match f with
  | BTrue -> "true"
  | BFalse -> "false"
  | BBitLit (width, value) ->
    Bigint.to_string value
  | BTable name ->
    "table_symb__" ^ name
  | BProj1 -> "first"
  | BProj2 -> "second"
  | BAction act ->
    "action_symb__" ^ act

let print_rel r : string =
  failwith "no relation symbols..."

let print_ident (printer: 'a -> string) (i: 'a Poulet4.Sig.ident) : string =
  let open Poulet4.Sig in
  match i with
  | SSimple n -> printer n
  | SIdx (n, args) ->
    Printf.sprintf "(_ %s %s)"
      (printer n)
      (List.map ~f:string_of_int args
       |> String.concat ~sep:" ")

let rec print_tm vp tm : string =
  let open Poulet4.Spec in
  match tm with
  | TVar x -> vp x
  | TFun (f, args) ->
    if List.length args > 0
    then Printf.sprintf "(%s %s)"
        (print_ident print_fun f)
        (print_tms vp args)
    else print_ident print_fun f

and print_tms vp tms : string =
  List.map ~f:(print_tm vp) tms
  |> String.concat ~sep:" "

let rec print_fm vp fm =
  let open Poulet4.Spec in
  match fm with
  | FTrue -> "true"
  | FFalse -> "false"
  | FEq (t1, t2) ->
    Printf.sprintf "(= %s %s)" (print_tm vp t1) (print_tm vp t2)
  | FRel (r, args) ->
    Printf.sprintf "(%s %s)" (print_rel r) (print_tms vp args)
  | FNeg f ->
    Printf.sprintf "(not %s)" (print_fm vp f)
  | FOr (f1, f2) ->
    Printf.sprintf "(or %s %s)" (print_fm vp f1) (print_fm vp f2)
  | FAnd (f1, f2) ->
    Printf.sprintf "(and %s %s)" (print_fm vp f1) (print_fm vp f2)
  | FImpl (f1, f2) ->
    Printf.sprintf "(=> %s %s)" (print_fm vp f1) (print_fm vp f2)

let sum_printer (v: (string, string) P4light.sum) : string =
  match v with
  | Coq_inl var -> Printf.sprintf "%s__l" var
  | Coq_inr var -> Printf.sprintf "%s__r" var

let check_refinement ((prog_l, prog_r), rel) =
  let wp =
    Poulet4.GGCL.Dijkstra.seq_prod_wp
      String.equal
      String.equal in
  match Poulet4.P4flatToGCL.prog_to_stmt prog_l Poulet4.P4flatToGCL.initial_p4sig,
        Poulet4.P4flatToGCL.prog_to_stmt prog_r Poulet4.P4flatToGCL.initial_p4sig with
  | Ok (prog_l_gcl, _), Ok (prog_r_gcl, _) ->
    let vc = wp prog_l_gcl prog_r_gcl rel in
    Printf.printf "(declare-const x_one_table__l Int)\n (declare-const x_seq_tables__r Int)\n \n (declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))\n (declare-fun table_symb__t_one_table (Int) (Pair Int Int))\n \n (declare-fun table_symb__t1_seq_tables (Int) (Pair Int Int))\n (declare-fun table_symb__t2_seq_tables (Int) (Pair Int Int))\n \n (define-const action_symb__nop Int 0)\n (define-const action_symb__set_x Int 1)\n";
    Printf.printf "\n(assert (not %s))\n(check-sat)\n(reset)\n" (print_fm sum_printer vc);
  | _, _ ->
    Printf.printf "prog_to_stmt failure"

let run_tbl () =
  let tests = Poulet4.Examples.refinements in
  List.iter ~f:check_refinement tests;
