module Petr4Info = Info
(* open Core  *)
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

let rec translate_lvalue (map: varmap) (e: Prog.Expression.t) : C.cexpr =
  match (snd e).expr with
  | Name (BareName str) -> CVar (snd str) 
  | _ -> failwith "translate_lvalue unimplemented"

let rec translate_expr (e: Prog.Expression.t) : C.cexpr =
  match (snd e).expr with
  | Name (BareName str) -> CVar (snd str) 
  | Name _ -> failwith "unimplemented"
  | ExpressionMember {expr; name} ->
     CMember (translate_expr expr, snd name)
  | True -> CBoolExp true
  | False -> CBoolExp false
  | Int i -> CIntLit (Bigint.to_int_exn (snd i).value)
  | Cast {expr; _} -> translate_expr expr
  | String s -> CString (snd s)
  | _ -> failwith "translate_expr unimplemented"

let rec get_expr_mem (e: Prog.Expression.t) : C.cname =
  match (snd e).expr with
  | Name name -> 
    begin match name with 
      | BareName str -> snd str
      | _ -> failwith "unimplemented" end
  | ExpressionMember x -> get_expr_mem x.expr 
  | _ -> failwith "unimplemented!"

let rec get_expr_mem_lst (e: Prog.Expression.t) : C.cname list =
  match (snd e).expr with
  | Name name -> 
    begin match name with 
      | BareName str -> [snd str]
      | _ -> failwith "unimplemented" end
  | ExpressionMember x -> get_expr_mem_lst x.expr @ [snd x.name] 
  | _ -> failwith "unimplemented!"

let translate_arg (map: varmap) (arg: Prog.Expression.t option) : C.cexpr =
  match arg with
  | Some expr -> translate_lvalue map expr
  | None -> failwith "don't care args unimplemented"

let translate_args (map: varmap) (args: Prog.Expression.t option list) : C.cexpr list =
  args
  |> List.map ~f:(translate_arg map)

let type_width hdr_type =
  let empty_env = Prog.Env.CheckerEnv.empty_t () in
  hdr_type
  |> Checker.min_size_in_bits empty_env Info.dummy
  |> Bigint.to_int_exn

let assert_packet_in (typ: Typed.Type.t) : unit =
  (* TODO actually check the type is appropriate? *)
  ()

let assert_packet_out (typ: Typed.Type.t) : unit =
  (* TODO actually check the type is appropriate? *)
  ()

let translate_stmt map (stmt: Prog.Statement.t) : C.cstmt =
  match (snd stmt).stmt with 
  | MethodCall {func = _, {expr = ExpressionMember {expr = pkt; name = (_, "extract")}; _};
                type_args = [hdr_typ];
                args} ->
    assert_packet_in (snd pkt).typ;
    let width = type_width hdr_typ in
    let args = translate_args map args in
    let pkt_arg = C.(CPointer (CVar "state", "pkt")) in
    C.CMethodCall (C.CVar "extract", pkt_arg :: args @ [C.CIntLit width])
  | MethodCall {func = _, {expr = ExpressionMember {expr = pkt; name = (_, "emit")}; _};
                type_args = [hdr_typ];
                args} ->
    assert_packet_out (snd pkt).typ;
    let width = type_width hdr_typ in
    let args = translate_args map args in
    let pkt_arg = C.(CPointer (CVar "state", "pkt")) in
    C.CMethodCall (C.CVar "emit", pkt_arg :: args @ [C.CIntLit width])
  | MethodCall {func = _, {expr = ExpressionMember {expr = obj; name = (_, "apply")}; _};
                type_args = [];
                args = []} ->
    CMethodCall (translate_expr obj, [CVar "state"])
  | MethodCall { func; type_args; args } -> 
    let args = translate_args map args in
    C.CMethodCall (translate_expr func, args)
  | Assignment { lhs; rhs } -> 
    C.CAssign (translate_lvalue map lhs, translate_expr rhs)
  | _ -> failwith "translate_stmt unimplemented"

let translate_stmts map (stmts: Prog.Statement.t list) : C.cstmt list =
  stmts
  |> List.map ~f:(translate_stmt map)

let translate_block map (block: Prog.Block.t) : C.cstmt list =
  (snd block).statements
  |> translate_stmts map

let get_type (typ: Typed.Type.t) : C.ctyp  =
  match typ with
  | Typed.Type.Bool -> C.CBool 
  | Typed.Type.TypeName (BareName n) ->
    C.CTypeName (snd n) 
  | Typed.Type.Bit {width = 8} ->
    C.CBit8
  | _ -> failwith "incomplete"

let add_param (state_name: string) (map: varmap) (param: Typed.Parameter.t) : varmap =
  let var = snd param.variable in
  let expr = C.CPointer (CVar state_name, var) in
  StrMap.update map var ~f:(fun _ -> expr)

let update_map (map : varmap ) (params : Typed.Parameter.t list) =
  match params with 
  | [] -> map 
  | h::t -> add_param "state" map h

let translate_key (key : Prog.Table.key) = 
  get_expr_mem_lst (snd key).key

let translate_local_decls (map: varmap) (d: Prog.Declaration.t list) : varmap * C.cdecl list * C.cstmt list =
  map, [], []

let rec translate_decl (map: varmap) (d: Prog.Declaration.t) : varmap * C.cdecl list =
  match snd d with
  | Struct {name; fields; _} ->
    let cfields = translate_fields fields in
    map, [C.CStruct (snd name, cfields)]
  | Header {name; fields; _} ->
    let cfields = translate_fields fields in
    let valid = C.CField (CBool, "__header_valid") in
    map, [C.CStruct (snd name, valid :: cfields)]
  | HeaderUnion {name; fields; _} ->
    map, [C.CComment "todo: Header union"]
  | Enum _
  | SerializableEnum _ ->
    map, [C.CComment "todo: Enum/SerializableEnum"]
  | Parser { name; type_params; params; constructor_params; locals; states; _} -> 
    let map_update = update_map map params in 
    let params = translate_params params in
    let state_type_name = make_state_name (snd name) in
    let state_type = C.(CPtr (CTypeName state_type_name)) in
    let state_param = C.CParam (state_type, "state") in
    let struct_decl = C.CStruct (state_type_name, params) in
    let map, locals_decls, locals_stmts = translate_local_decls map locals in
    let state_stmts = translate_parser_states map states in
    let func_decl = C.CFun (CVoid, snd name, [state_param], locals_stmts @ state_stmts) in
    map_update, struct_decl :: locals_decls @ [func_decl]
  | Function { return; name; type_params; params; body } ->
    map, [C.CComment "todo: Function"]
  | Action { name; data_params; ctrl_params; body; _ } -> 
    map, [C.CComment "todo: Action"]
  | Control { name; type_params; params; constructor_params; locals; apply; _ } ->
    let flat_params = params@constructor_params in  
    let map_update = update_map map flat_params in 
    let params = translate_params flat_params in
    let state_type_name = make_state_name "_state" in
    let state_type = C.(CPtr (CTypeName state_type_name)) in
    let state_param = C.CParam (state_type, "state") in
    let struct_decl = C.CStruct (state_type_name, params) in
    let locals_translate = List.map ~f:(translate_local (snd name) map) locals in 
    let func_decl = 
      C.CFun (CVoid, snd name, [state_param], 
              translate_block map_update apply) in 
    map_update, struct_decl :: locals_translate @ [func_decl] 
  | Constant _ ->
    map, [C.CComment "todo: Constant"]
  | Instantiation _ ->
    map, [C.CComment "todo: Instantiation"]
  | Variable _ ->
    map, [C.CComment "todo: Variable"]
  | Table _ -> 
    map, [C.CComment "todo: Table"]
  | ValueSet _
  | ControlType _
  | ParserType _
  | PackageType _
  | ExternObject _
  | ExternFunction _
  | Error _
  | MatchKind _
  | NewType _
  | TypeDef _ ->
    map, []

and translate_decls (map: varmap) (decls: Prog.Declaration.t list) : varmap * C.cdecl list =
  let f (map, decls) decl =
    let map', decls' = translate_decl map decl in
    map', decls @ decls'
  in
  List.fold ~init:(map, []) ~f decls

and translate_local (control_name: string) (map: varmap) (locals : Prog.Declaration.t) : C.cdecl = 
  match snd locals with 
  | Action { name; data_params; ctrl_params; body; _ } -> 
    C.CFun (CVoid, snd name, 
            [CParam (CTypeName "MyC_state", "*state")], 
            translate_block map body)
  | Table { name; key; actions; entries; default_action; size; custom_properties; _ } ->
    translate_table(control_name, snd name, key, actions, entries, default_action, size, custom_properties)
  | _ -> failwith "incomplete"

and find_table_name (locals : Prog.Declaration.t list) : string =
  let f decl = 
    match snd decl with 
    | Prog.Declaration.Table {name;_} -> Some (snd name) 
    | _ -> None
  in List.find_map_exn locals ~f

and ext_action (lst : Prog.Expression.t option ) =
  begin match lst with 
    | None -> failwith "unimplemented" 
    | Some s -> begin match (snd s).expr with
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
        | _ -> failwith "uni"
      end 
  end 

and get_default_action (action : Prog.Table.action_ref option) = 
  match action with
  | None -> failwith "unimplemented"
  | Some h -> ((snd h).action).name

and get_action_ref (actions : Prog.Table.action_ref list) = 
  match actions with
  | [] -> []
  | h::t -> let n = snd h 
    in  [(n.action).name] @ get_action_ref t

and get_name (n: P4.name) = 
  match n with 
  | BareName b -> b
  | _ -> failwith "faa"

and get_cond_logic_lst (entries : Prog.Table.entry list option) (keylist : Prog.Table.key list) : C.cexpr list =
  List.map ~f:(get_cond_logic entries) keylist 

(* todo: keylist instead of key  *)
and get_cond_logic (entries : Prog.Table.entry list option) (key : Prog.Table.key) =
  match entries with 
  | None -> failwith "n"
  | Some e -> begin match e with 
      | [] -> failwith "af"
      | h::t -> let m = (snd h).matches in
        (* instead of handling only len 1 for m, get it to handle all lengths *)
        let equal = begin match m with 
          | [] -> failwith "F"
          | (_, {expr = Prog.Match.Expression {expr}; _})::t -> expr 
          | _ -> failwith "ddf"
        end in 
        C.CEq (translate_pointer (C.CVar "state") key, translate_expr equal) 
    end 

and translate_pointer (pointer : C.cexpr) (pointee : Prog.Table.key) = 
  let key_lst = translate_key pointee in 
  let base (x: C.cname) = C.CPointer (pointer, x) in 
  let f (index: int) (acc: C.cname -> C.cexpr) (el: C.cname) (x : C.cname) = 
    if index = List.length key_lst - 1 then 
      acc el 
    else 
      C.CMember (acc el, x) in
  List.foldi ~init:base ~f:f key_lst "" 

and get_entry_methods (entries : Prog.Table.entry list option) =
  match entries with 
  | None -> failwith "n"
  | Some e -> 
    let rec get_entry_methods_internal (lst : Prog.Table.entry list) = match lst with 
      | [] -> []
      | h::t -> [((snd h).action)] @ get_entry_methods_internal t  in
    let l = get_entry_methods_internal e in 
    get_action_ref l 

and make_state_name =
  Printf.sprintf "%s_state" 

and translate_inner ((k : Prog.Table.key list), (entries : Prog.Table.entry list option), (default_action : Prog.Table.action_ref option)) : C.cstmt = 
  (* todo - deal with multiple keys  *)
  (* todo - ternary matches in entries - spec value and bit mask (e.g. or with a mask), prefix matches  *)
  match k with 
  | [] -> failwith "empty key list" 
  | key::key_end -> 
    begin match entries with 
      | None -> failwith "f"
      | Some s -> begin match s with 
          | [] -> method_call_table (get_default_action default_action)
          | h::t -> C.CIf 
                      (get_cond_logic entries key, method_call_table_entry h, translate_inner(k, Some t, default_action)) 
        end 
    end 


and translate_table(control_name, name, k, actions, entries, default_action, size, custom_properties) = 
  let state_type = C.(CPtr (CTypeName (make_state_name control_name))) in
  let state_param = C.CParam (state_type, "state") in
  C.CFun(C.CVoid, name, [state_param], [translate_inner (k, entries, default_action)]) 

and method_call_table (name : P4.name) = 
  C.CMethodCall (C.CVar (snd (get_name name)), [C.CVar "state"])

and method_call_table_entry (entry : Prog.Table.entry) = 
  let n = snd (snd entry).action in 
  C.CMethodCall (C.CVar (snd (get_name (n.action).name)), [C.CVar "state"])

and get_first (list) = 
  match list with 
  | h::t -> h
  | _ -> failwith "empty"

and translate_parser_locals (locals: Prog.Declaration.t list) : C.cstmt list =
  []

and translate_parser_states map (states: Prog.Parser.state list) : C.cstmt list =
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
    |> List.map ~f:(translate_parser_state map states_map)
  in
  let start_id = Map.find_exn states_map "start" in
  C.[CVarInit (CInt, next_state_name, CIntLit start_id);
     CWhile (CGeq (next_state_var, CIntLit 0),
             CSwitch (next_state_var, cases))]

and translate_parser_state map (states: int StrMap.t) (state: Prog.Parser.state) : C.ccase =
  let stmts = translate_stmts map (snd state).statements in
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
  | _ -> failwith "incomplete"

let translate_prog ((Program prog): Prog.program) : C.cprog =
  prog
  |> translate_decls StrMap.empty
  |> snd

let compile (prog: Prog.program) : C.cprog =
  CInclude "petr4-runtime.h" ::
  translate_prog prog
