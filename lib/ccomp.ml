module Petr4Info = Info
open Core_kernel
module Info = Petr4Info
module C = Csyntax
module P4 = Types

module Map = Map.Make(String)
module Env = struct
  type t = C.cexpr Map.t
end

(* Type of a compiler producing syntax in 'a. *)
type 'a comp = Env.t -> (Env.t * 'a) option

module CompOps = struct
  type 'a t = 'a comp

  let bind (c: 'a t) ~f:(f:'a -> 'b t) : 'b t = fun env ->
    match c env with
    | Some (env', a) -> f a env'
    | None -> None

  let return (a: 'a) =
    fun env -> Some (env, a)

  let map = `Define_using_bind

  let find_var (var: string) : (C.cexpr option) t =
    fun env -> Some (env, Map.find env var)

  let fail = fun env -> None
end

module CompM = Monad.Make(CompOps)

open CompM.Let_syntax

let next_state_name = "__next_state"
let next_state_var = C.CVar next_state_name

let get_expr_name (e: Prog.Expression.t) : C.cname =
  match (snd e).expr with
  | ExpressionMember x -> snd x.name
  | FunctionCall x -> failwith "a"
  | NamelessInstantiation x -> failwith "b"
  | String s -> failwith (snd s)
  | Mask x -> failwith "dsjak"
  | Name n -> begin match n with 
      | BareName str -> snd str
      | _ -> failwith "unimplemented" end 
  | True ->  "true"
  | False -> "false"
  | _ -> failwith "unimplementeddj"

let get_expr_c (e: Prog.Expression.t) : C.cexpr =
  match (snd e).expr with
  | Name n -> begin match n with 
      | BareName str -> CString (snd str) 
      | _ -> failwith "unimplemented" end 
  | True ->  CBoolExp true  
  | False -> CBoolExp false   
  | _ -> failwith "unimpl"

let rec get_expr_mem (e: Prog.Expression.t) : C.cname =
  match (snd e).expr with
  | Name name -> 
    begin match name with 
      | BareName str -> snd str
      | _ -> failwith "unimplemented" end
  | ExpressionMember x -> get_expr_mem x.expr 
  | _ -> failwith "unimplemented!"

let rec get_expr_opt_lst (e: Prog.Expression.t option list) : C.cexpr list =
  match e with
  | [] -> []
  | h::t ->
    let fst =
      match h with 
      | None -> C.CVar "don't care compilation unimplemented"
      | Some s -> begin match (snd s).expr with
          | Name name -> 
            begin match name with 
              | BareName str -> CVar (snd str)
              | _ -> failwith "unimplemented--" end
          | ExpressionMember {expr; name} ->
            CAddrOf (CPointer (CMember ((CVar "state"), get_expr_mem expr), snd name))
          | _ -> failwith "unimplemented!"
        end
    in
    fst::get_expr_opt_lst t  

let translate_expr_comp (e: Prog.Expression.t) : C.cexpr comp =
  match (snd e).expr with
  | Name (BareName x) ->
    begin match%bind CompOps.find_var (snd x) with
      | Some e -> e |> return
      | None -> C.CVar (snd x) |> return
    end
  | _ -> (C.CIntLit 123) |> return

let type_width hdr_type =
  let empty_env = Prog.Env.CheckerEnv.empty_t () in
  hdr_type
  |> Checker.min_size_in_bits empty_env Info.dummy
  |> Bigint.to_int_exn

let assert_packet_in (typ: Typed.Type.t) : unit =
  (* TODO actually check the type is appropriate? *)
  ()

let translate_stmt (stmt: Prog.Statement.t) : C.cstmt comp =
  match (snd stmt).stmt with 
  | MethodCall {func = _, {expr = ExpressionMember {expr = pkt; name = (_, "extract")}; _};
                type_args = [hdr_typ];
                args} ->
    assert_packet_in (snd pkt).typ;
    let width = type_width hdr_typ in
    let args = get_expr_opt_lst args in
    let pkt_arg = C.(CPointer (CVar "state", "pkt")) in
    C.CMethodCall ("extract", pkt_arg :: args @ [C.CIntLit width]) |> return
  | _ -> C.CVarInit (CInt, "todo", CIntLit 123) |> return

let translate_stmts (stmts: Prog.Statement.t list) : (C.cstmt list) comp =
  stmts
  |> List.map ~f:translate_stmt
  |> CompM.all

let rec translate_decl (d: Prog.Declaration.t) : (C.cdecl list) comp =
  match snd d with
  | Struct {name; fields; _} ->
    let%bind cfields = translate_fields fields in
    [C.CStruct (snd name, cfields)] |> return
  | Header {name; fields; _} ->
    let%bind cfields = translate_fields fields in
    let valid = C.CField (CBool, "__header_valid") in
    [C.CStruct (snd name, valid :: cfields)] |> return
  | Parser { name; type_params; params; constructor_params; locals; states; _} -> 
    let%bind params = translate_params params in
    let state_type_name = snd name ^ "_state" in
    let state_type = C.(CPtr (CTypeName state_type_name)) in
    let state_param = C.CParam (state_type, "state") in
    let struct_decl = C.CStruct (state_type_name, params) in
    let%bind locals_stmts = translate_parser_locals locals in
    let%bind state_stmts = translate_parser_states states in
    let func_decl = C.CFun (CVoid, snd name, [state_param], locals_stmts @ state_stmts) in
    [struct_decl; func_decl] |> return
  | Function { return; name; type_params; params; body } -> failwith "Fds"
  | Action { name; data_params; ctrl_params; body; _ } -> 
    [C.CInclude ("fdjskfldsjkfldsjkflds")] |> return 
  | Control { name; type_params; params; constructor_params; locals; apply; _ } ->
    let%bind params = translate_params params in
    let app_block = (List.map ~f:translate_act locals) in 
    [C.CDecList ([C.CStruct (snd name, params)] @ 
                 app_block @
                 [C.CFun (CVoid, snd name ^ "_fun", 
                          [CParam (CTypeName (snd name), "*state")], 
                          apply_translate_emit apply)])]  |> return 
  | _ -> [C.CInclude "todo"] |> return 

and translate_act (locals : Prog.Declaration.t) : C.cdecl = 
  match snd locals with 
  | Action { name; data_params; ctrl_params; body; _ } -> 
    C.CFun (CVoid, snd name, 
            [CParam (CTypeName "C_state", "*state")], 
            apply_translate_emit body)
  | _ -> C.CInclude "not needed"

and translate_parser_locals (locals: Prog.Declaration.t list) : (C.cstmt list) comp =
  return []

and translate_parser_states (states: Prog.Parser.state list) : (C.cstmt list) comp =
  let add_state idx map (state: Prog.Parser.state) =
    Map.add_exn map ~key:(snd (snd state).name) ~data:idx
  in
  let states_map =
    states
    |> List.foldi ~init:Map.empty ~f:add_state
    |> Map.add_exn ~key:"accept" ~data:(-1)
    |> Map.add_exn ~key:"reject" ~data:(-2)
  in
  let%bind cases = 
    states
    |> List.map ~f:(translate_parser_state states_map)
    |> CompM.all
  in
  let start_id = Map.find_exn states_map "start" in
  return C.[CVarInit (CInt, next_state_name, CIntLit start_id);
            CWhile (CGeq (next_state_var, CIntLit 0),
                    CSwitch (next_state_var, cases))]

and translate_parser_state (states: int Map.t) (state: Prog.Parser.state) : C.ccase comp =
  let%bind stmts = translate_stmts (snd state).statements in
  let%bind annot = translate_trans states (snd state).transition in
  let state_id = Map.find_exn states (snd (snd state).name) in
  C.(CCase (CIntLit state_id, stmts @ annot)) |> return

and translate_trans (states: int Map.t) (t: Prog.Parser.transition) : (C.cstmt list) comp =
  match snd t with
  | Direct {next} ->
    let nextid = Map.find_exn states (snd next) in
    return C.[CAssign (next_state_var, CIntLit nextid)]
  | Select _ ->
    failwith "translation of select() unimplemented"

and translate_fun (s:Prog.Statement.t) : C.cstmt = 
  match (snd s).stmt with 
  | MethodCall { func; type_args; args } -> 
    let state_arg = C.(CPointer (CVar "state", get_expr_mem func)) in
    let args = state_arg :: get_expr_opt_lst args @ [CIntLit 16] in
    C.CMethodCall (get_expr_name func, args)
  | Assignment { lhs; rhs } -> C.CAssign ((get_expr_c lhs), (get_expr_c rhs)) 
  | _ ->  C.CMethodCall ("hold", [CVar "param"]) 

and apply_translate_emit (apply : Prog.Block.t) = 
  let stmt = (snd apply).statements in 
  List.map ~f:translate_fun stmt 

and translate_extract (s : Prog.Parser.state list) : C.cstmt list= 
  match s with 
  | [] -> failwith "empty"
  | h::t -> 
    match snd h with 
    | { annotations; name; statements; transition } -> List.map ~f:translate_fun statements

and translate_param (param : Typed.Parameter.t) : C.cfield comp =
  let%bind ctyp = translate_type param.typ in
  C.CField (ctyp, snd param.variable) |> return

and translate_params (params : Typed.Parameter.t list) : C.cfield list comp=
  params
  |> List.map ~f:translate_param
  |> CompM.all

and translate_field (field: Prog.Declaration.field) : C.cfield comp =
  let%bind ctyp = translate_type (snd field).typ in
  C.CField (ctyp, snd (snd field).name) |> return

and translate_fields (fields: Prog.Declaration.field list) =
  fields
  |> List.map ~f:translate_field
  |> CompM.all

and translate_type (typ: Typed.Type.t) : C.ctyp comp =
  match typ with
  | Typed.Type.Bool -> C.CBool |> return
  | Typed.Type.TypeName (BareName n) ->
    C.CTypeName (snd n) |> return
  | Typed.Type.Bit {width = 8} ->
    C.CBit8 |> return
  | _ -> C.CInt |> return

let translate_prog ((Program t): Prog.program) : C.cprog comp =
  t
  |> List.map ~f:translate_decl
  |> CompM.all
  >>| List.concat

let compile (prog: Prog.program) : C.cprog =
  CInclude "petr4-runtime.h" ::
  match translate_prog prog Map.empty with
  | Some result -> snd result
  | None -> failwith "compilation failed (todo error message)"
