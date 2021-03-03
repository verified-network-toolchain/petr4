module Petr4Info = Info
open Core_kernel
module Info = Petr4Info
module C = Csyntax
module P4 = Types

module StrMap = Map.Make(String)
type varmap = C.cexpr StrMap.t

let varmap_find (map: varmap) (var: string) : C.cexpr =
  match StrMap.find map var with
  | Some expr -> expr
  | None -> C.CVar var

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

let translate_expr (map: varmap) (e: Prog.Expression.t) : C.cexpr =
  match (snd e).expr with
  | Name (BareName (_, x)) ->
    varmap_find map x
  | _ -> C.CIntLit 12355

let type_width hdr_type =
  let empty_env = Prog.Env.CheckerEnv.empty_t () in
  hdr_type
  |> Checker.min_size_in_bits empty_env Info.dummy
  |> Bigint.to_int_exn

let assert_packet_in (typ: Typed.Type.t) : unit =
  (* TODO actually check the type is appropriate? *)
  ()

let translate_stmt (stmt: Prog.Statement.t) : C.cstmt =
  match (snd stmt).stmt with 
  | MethodCall {func = _, {expr = ExpressionMember {expr = pkt; name = (_, "extract")}; _};
                type_args = [hdr_typ];
                args} ->
    assert_packet_in (snd pkt).typ;
    let width = type_width hdr_typ in
    let args = get_expr_opt_lst args in
    let pkt_arg = C.(CPointer (CVar "state", "pkt")) in
    C.CMethodCall ("extract", pkt_arg :: args @ [C.CIntLit width])
  | _ -> C.CVarInit (CInt, "todo", CIntLit 123)

let translate_stmts (stmts: Prog.Statement.t list) : C.cstmt list =
  stmts
  |> List.map ~f:translate_stmt

let get_type (typ: Typed.Type.t) : C.ctyp  =
  match typ with
  | Typed.Type.Bool -> C.CBool 
  | Typed.Type.TypeName (BareName n) ->
    C.CTypeName (snd n) 
  | Typed.Type.Bit {width = 8} ->
    C.CBit8
  | _ -> C.CInt 

let add_param (state_name: string) (map: varmap) (param: Typed.Parameter.t) : varmap =
  let var = snd param.variable in
  let expr = C.CPointer (CVar state_name, var) in
  StrMap.add_exn map ~key:var ~data:expr

let update_map (map : varmap ) (params : Typed.Parameter.t list) =
  match params with 
  | [] -> map 
  | h::t -> add_param "state" map h

let translate_key (key : Prog.Table.key) = 
  get_expr_name (snd key).key

let rec translate_decl (map: varmap) (d: Prog.Declaration.t) : varmap * C.cdecl list =
  match snd d with
  | Struct {name; fields; _} ->
    let cfields = translate_fields fields in
    map, [C.CStruct (snd name, cfields)]
  | Header {name; fields; _} ->
    let cfields = translate_fields fields in
    let valid = C.CField (CBool, "__header_valid") in
    map, [C.CStruct (snd name, valid :: cfields)]
  | Parser { name; type_params; params; constructor_params; locals; states; _} -> 
    let map_update = update_map map params in 
    let params = translate_params params in
    let state_type_name = snd name ^ "_state" in
    let state_type = C.(CPtr (CTypeName state_type_name)) in
    let state_param = C.CParam (state_type, "state") in
    let struct_decl = C.CStruct (state_type_name, params) in
    let locals_stmts = translate_parser_locals locals in
    let state_stmts = translate_parser_states states in
    let func_decl = C.CFun (CVoid, snd name, [state_param], locals_stmts @ state_stmts) in
    map_update, [struct_decl; func_decl]
  | Function { return; name; type_params; params; body } -> failwith "Fds"
  | Action { name; data_params; ctrl_params; body; _ } -> 
    map, [C.CInclude ("fdjskfldsjkfldsjkflds")] 
  | Control { name; type_params; params; constructor_params; locals; apply; _ } ->
    let fields = translate_params params in
    let state_struct = C.CStruct (snd name, fields) in
    let app_block = List.map ~f:(translate_act map) locals in 
    map, state_struct ::
         app_block @
         [C.CFun (CVoid, snd name ^ "_fun", 
                  [CParam (CPtr (CTypeName (snd name)), "state")], 
                  apply_translate_emit map apply)]
  | _ -> map, [C.CInclude "todo"] 

and translate_act (map: varmap) (locals : Prog.Declaration.t) : C.cdecl = 
  match snd locals with 
  | Action { name; data_params; ctrl_params; body; _ } -> 
    C.CFun (CVoid, snd name, 
            [CParam (CTypeName "C_state", "*state")], 
            apply_translate_emit map body)
  | Table { name; key; actions; entries; default_action; size; custom_properties; _ } -> 
    begin match key with 
      | [] -> failwith "nothing"
      (* problem - where should C actually come from? The map? *)
      (* problem - the parameter for the void function should be in the map, but need a 
         type of block to get it - I dont have acces to that info here *)
      (* problem - key is .dst, not the entire hdrs.simple.dst *)
      | [k] -> C.CFun 
                 (CVoid, "C", [CParam (CTypeName "C_state", "*state")], 
                  C.[CIf ((C.CPointer ((C.CString "state"), "hdrs.simple.dst != 0")),
                          (CMethodCall ("C_do_forward", [C.CString "state"])),
                          (CMethodCall ("C_do_drop", [C.CString "state"])))])
      | _ -> failwith "no" end 
  | _ -> C.CInclude "not needed"

and translate_parser_locals (locals: Prog.Declaration.t list) : C.cstmt list =
  []

and translate_parser_states (states: Prog.Parser.state list) : C.cstmt list =
  let add_state idx map (state: Prog.Parser.state) =
    Map.add_exn map ~key:(snd (snd state).name) ~data:idx
  in
  let states_map =
    states
    |> List.foldi ~init:StrMap.empty ~f:add_state
    |> Map.add_exn ~key:"accept" ~data:(-1)
    |> Map.add_exn ~key:"reject" ~data:(-2)
  in
  let cases = 
    states
    |> List.map ~f:(translate_parser_state states_map)
  in
  let start_id = Map.find_exn states_map "start" in
  C.[CVarInit (CInt, next_state_name, CIntLit start_id);
     CWhile (CGeq (next_state_var, CIntLit 0),
             CSwitch (next_state_var, cases))]

and translate_parser_state (states: int StrMap.t) (state: Prog.Parser.state) : C.ccase =
  let stmts = translate_stmts (snd state).statements in
  let annot = translate_trans states (snd state).transition in
  let state_id = Map.find_exn states (snd (snd state).name) in
  C.(CCase (CIntLit state_id, stmts @ annot))

and translate_trans (states: int StrMap.t) (t: Prog.Parser.transition) : C.cstmt list =
  match snd t with
  | Direct {next} ->
    let nextid = Map.find_exn states (snd next) in
    C.[CAssign (next_state_var, CIntLit nextid)]
  | Select _ ->
    failwith "translation of select() unimplemented"

and translate_fun (map: varmap) (s: Prog.Statement.t) : C.cstmt = 
  match (snd s).stmt with 
  | MethodCall { func; type_args; args } -> 
    (* let state_arg = StrMap.find_exn map (get_expr_mem func) in *)
    (* let args = state_arg :: get_expr_opt_lst args @ [CIntLit 16] in *)
    let args = get_expr_opt_lst args @ [CIntLit 16] in
    C.CMethodCall (get_expr_name func, args)
  | Assignment { lhs; rhs } -> 
    let left = C.CPointer ((C.CString "state"), (get_expr_name lhs)) in 
    C.CAssign (left, (get_expr_c rhs)) 
  | _ ->  C.CMethodCall ("hold", [CVar "param"]) 

and apply_translate_emit (map: varmap) (apply : Prog.Block.t) = 
  let stmt = (snd apply).statements in 
  List.map ~f:(translate_fun map) stmt 

and translate_extract (map: varmap) (s : Prog.Parser.state list) : C.cstmt list =
  match s with 
  | [] -> failwith "empty"
  | h::t -> 
    match snd h with 
    | { annotations; name; statements; transition } -> List.map ~f:(translate_fun map) statements

and translate_param (param : Typed.Parameter.t) : C.cfield =
  let ctyp = translate_type param.typ in
  C.CField (ctyp, snd param.variable)

and translate_params (params : Typed.Parameter.t list) : C.cfield list =
  params
  |> List.map ~f:translate_param

and translate_field (field: Prog.Declaration.field) : C.cfield =
  let ctyp = translate_type (snd field).typ in
  C.CField (ctyp, snd (snd field).name)

and translate_fields (fields: Prog.Declaration.field list) =
  fields
  |> List.map ~f:translate_field

and translate_type (typ: Typed.Type.t) : C.ctyp =
  match typ with
  | Typed.Type.Bool -> C.CBool
  | Typed.Type.TypeName (BareName n) ->
    C.CTypeName (snd n)
  | Typed.Type.Bit {width = 8} ->
    C.CBit8
  | _ -> C.CInt

let translate_prog ((Program t): Prog.program) : C.cprog =
  let init = StrMap.empty, [] in
  let f (map, decls) decl =
    let map', decls' = translate_decl map decl in
    map', decls @ decls'
  in
  t
  |> List.fold ~init ~f
  |> snd

let compile (prog: Prog.program) : C.cprog =
  CInclude "petr4-runtime.h" ::
  translate_prog prog
