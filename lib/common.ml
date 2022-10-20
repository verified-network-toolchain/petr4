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

  let check_prog
        (include_dirs : string list)
        (p4_file : string) 
        (normalize : bool)
        (gen_loc : bool)
        (verbose : bool) =
    match parse_file include_dirs p4_file verbose with
    | `Ok prog ->
       let prog, renamer = Elaborate.elab prog in
       let _, typed_prog = Checker.check_program renamer prog in
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
       `Ok prog''
    | `Error e ->
       `Error e

  let check_file
        (include_dirs : string list)
        (p4_file : string) 
        (exportp4 : bool)
        (exportp4_ocaml: bool)
        (normalize : bool)
        (export_file : string)
        (gen_loc : bool)
        (verbose : bool) 
        (printp4 : bool)
        (printp4_file: string)
      : unit =
    match check_prog include_dirs p4_file normalize gen_loc verbose with
    | `Ok prog ->
       Format.printf "%a" pretty prog;
       begin 
         if exportp4 then
           let oc = Out_channel.create export_file in
           Exportp4.print_program (Format.formatter_of_out_channel oc) prog;
           Out_channel.close oc
       end;
       begin 
         if exportp4_ocaml then
           let oc = Out_channel.create export_file in
           Exportp4prune.print_program (Format.formatter_of_out_channel oc) prog;
           Out_channel.close oc
       end;
       begin
         if printp4 then
           let oc_p4 = Out_channel.create printp4_file in
           Printp4.print_program (Format.formatter_of_out_channel oc_p4)
             ["core.p4"; "tna.p4";"common/headers.p4";"common/util.p4"] 
             ["@pragma pa_auto_init_metadata"]
             prog;
           Out_channel.close oc_p4
       end
    | `Error (info, Lexer.Error s) ->
       Format.eprintf "%s: %s@\n%!" (P4info.to_string info) s
    | `Error (info, Parser.Error) ->
      Format.eprintf "%s: syntax error@\n%!" (P4info.to_string info)
    | `Error (info, err) ->
      Format.eprintf "%s: %s@\n%!" (P4info.to_string info) (Exn.to_string err)

 let write_p4cub_to_file prog printp4_file =
   let oc_p4 = Out_channel.create printp4_file in
   Printp4cub.print_prog (Format.formatter_of_out_channel oc_p4) prog;
   Out_channel.close oc_p4

 let to_p4cub light =
   let open Poulet4 in
   match ToP4cub.translate_program P4info.dummy light with
   | Result.Ok cub -> cub
   | Result.Error e -> failwith e

 let gen_loc ~if_:do_gen_loc light =
   if do_gen_loc then begin
     match Poulet4.GenLoc.transform_prog P4info.dummy light with
     | Coq_inl located_light -> located_light 
     | Coq_inr ex -> failwith "error occurred in GenLoc"
     end
   else light

 let print_type_def (oc) (struc : string) (typ : string) : unit = 
    Printf.fprintf oc "typedef struct %s %s; \n" struc typ

 let simpl_expr ~do_simpl_expr light =
   if do_simpl_expr then
     Poulet4.SimplExpr.transform_prog P4info.dummy light
   else
     light

 let to_gcl (p4cub : Poulet4.ToP4cub.coq_DeclCtx) gas unroll =
   let open Poulet4 in
   let coq_gcl = V1model.gcl_from_p4cub TableInstr.instr gas unroll p4cub in
   match coq_gcl with
   | Result.Error msg -> failwith msg
   | Result.Ok gcl -> gcl
   
 let ccompile cub =
   match Poulet4_Ccomp.CCompSel.coq_Compile cub with
   | Poulet4_Ccomp.Errors.OK c ->     
     c
   | Poulet4_Ccomp.Errors.Error (m) ->
     match m with
     | (Poulet4_Ccomp.Errors.MSG msg) ::[] ->
       failwith (Base.String.of_char_list msg)
     | _ ->
       failwith ("unknown failure from Ccomp") 
   

 let flatten cub =
   Poulet4.ToP4cub.flatten_DeclCtx cub
   
 let to_c print file cub =  
   (* the C compiler *)
   let cub = flatten cub in
   let stmtd = Poulet4.Statementize.lift_program cub in
   (if print then write_p4cub_to_file stmtd file);
   let certd : Poulet4_Ccomp.AST0.TopDecl.d list = List.map ~f:Compcertalize.topdecl_convert cub in 
   ccompile certd
   
                    
 let compile_file (include_dirs : string list) (p4_file : string) 
     (normalize : bool) (export_file : string) (verbose : bool)
     (do_gen_loc : bool) (print_p4cub : bool)
     (printp4_file : string)
     (gcl : int list)
     : unit =
   match parse_file include_dirs p4_file verbose with
   | `Ok prog ->
     let prog, renamer = Elaborate.elab prog in
     let _, typ_light = Checker.check_program renamer prog in
     (* Preprocessing  *)
     let nrm_light = simpl_expr ~do_simpl_expr:normalize typ_light in
     let loc_light = gen_loc    ~if_:do_gen_loc nrm_light in
     (*let hoist =
       begin match Poulet4.HoistNameless.hoist_nameless_instantiations (simpl_expr ~if_:true  loc_light) with
       | Ok p -> p
       | _ -> failwith "hoist failed"
       end in
     let (_,inline_types) = Poulet4.InlineTypeDecl.inline_typ_program Poulet4.Maps.IdentMap.empty hoist in
     print_endline "\n------------------ p4light ------------------\n";
     Printp4.print_decls Format.std_formatter inline_types;*)
     (* p4cub compiler *)
     (*Printp4.print_decls Format.std_formatter loc_light;*)
     let cub = to_p4cub loc_light in
     (*print_endline "\n========================= p4cub ========================\n";
     Printp4cub.print_prog Format.std_formatter (Poulet4.ToP4cub.flatten_DeclCtx cub);*)
     begin match gcl with
     | [gas; unroll] ->
       (* GCL Compiler *)
       let _ = to_gcl cub gas unroll in
       Printf.printf "No Error converting to GCL\n%!"
     | [] ->
       (* the C compiler *)
       Poulet4_Ccomp.PrintClight.change_destination export_file;       
       let ((prog, hid), mid) = to_c print_p4cub printp4_file cub in
       Poulet4_Ccomp.CCompSel.print_Clight prog;
       (let oc = Out_channel.create ~append:true  export_file in 
        begin (
          print_type_def oc (Poulet4_Ccomp.PrintCsyntax.name_of_ident hid) "H";
          print_type_def oc (Poulet4_Ccomp.PrintCsyntax.name_of_ident mid) "M"
        )end)
       
     | _ ->
       failwith "unrecognized arguments to -gcl"
     end
   | `Error (info, Lexer.Error s) ->
     Format.eprintf "%s: %s@\n%!" (P4info.to_string info) s
   | `Error (info, Parser.Error) ->
     Format.eprintf "%s: syntax error@\n%!" (P4info.to_string info)
   | `Error (info, err) ->
     Format.eprintf "%s: %s@\n%!" (P4info.to_string info) (Exn.to_string err)
       
 let parse_hex_pkt (s : string) : bool list =
   s
   |> Cstruct.of_hex
   |> Cstruct.to_string
   |> Util.string_to_bits

 let eval_file include_dirs p4_file verbose pkt_str port target =
   let st = fun _ -> None in
   let port = Bigint.of_int port in
   let pkt = parse_hex_pkt pkt_str in
   match check_prog include_dirs p4_file true true verbose with
   | `Ok prog ->
      begin match target with
      | "v1" ->
         begin match Eval.v1_interp prog st port pkt with
         | Ok ((st, port), pkt) -> `Ok (pkt, port)
         | Error e -> e |> Poulet4.Target.Exn.to_string |> failwith
         end
      (*
      | "ebpf" ->
      let st = EbpfInterpreter.empty_state in
      begin match EbpfInterpreter.eval_program (([],[]), vsets) env st pkt port typed_prog |> snd with
      | Some (pkt, port) -> `Ok(pkt,port)
      | None -> `NoPacket
      end
      *)
      | _ -> Format.sprintf "Architecture %s unsupported" target |> failwith
      end
   | `Error (info, exn) as e -> e
 
  let eval_file_string include_dirs p4_file verbose pkt_str port target =
    match eval_file include_dirs p4_file verbose pkt_str port target with
    | `Ok (pkt, port) ->
       Printf.sprintf "%s on port: %s\n"
         (pkt
          |> Util.bits_to_string
          |> Util.hex_of_string)
         (Bigint.to_string port)
    | `NoPacket -> "No packet out"
    | `Error (info, exn) ->
      let exn_msg = Exn.to_string exn in
      let info_string = P4info.to_string info in
      info_string ^ "\n" ^ exn_msg

end
