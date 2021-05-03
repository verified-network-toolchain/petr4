module Petr4Info = Info
(* open Core  *)
open Core_kernel
module Info = Petr4Info
module C = Csyntax

module StrMap = Map.Make(String)

type table_summary =
  { key: Prog.Table.key list;
    actions: Prog.Table.action_ref list;
    entries: (Prog.Table.entry list) option;
    default_action: Prog.Table.action_ref option;
    size: Prog.P4Int.t option;
    custom_properties: Prog.Table.property list }

type table_map = table_summary StrMap.t

let next_state_name = "__next_state"

let next_state_var = C.CVar next_state_name

let rec translate_expr (e: Prog.Expression.t) : C.cexpr =
  match (snd e).expr with
  | Name (BareName str) -> C.CVar (snd str)
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

let translate_arg (dir: Typed.direction) (arg: Prog.Expression.t option) : C.cexpr =
  match arg with
  | Some expr ->
     begin match dir with
     | Out
     | InOut ->
        C.CAddrOf (translate_expr expr)
     | _ ->
        translate_expr expr
     end
  | None -> failwith "don't care args unimplemented"

let translate_args (args: Prog.Expression.t option list) : C.cexpr list =
  args
  |> List.map ~f:(translate_arg In) (*TODO use actual direction*)

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

let cast_to_void_ptr (e: C.cexpr) : C.cexpr =
  C.CCast (CPtr CVoid, e)

let rec get_name (n: Types.name) = 
  match n with 
  | BareName b -> b
  | _ -> failwith "faa"

and build_action_map actions =
  let f map (act: Prog.Table.action_ref) =
    let act = (snd act).action in
    map
    |> StrMap.add_exn ~key:(act.name |> get_name |> snd) ~data:act.args
  in
  List.fold ~f ~init:StrMap.empty actions

and translate_table_apply map tbl_name =
  let {key; actions; entries; default_action; size; custom_properties} =
    StrMap.find_exn map tbl_name
  in
  let action_map = build_action_map actions in
  let entries =
    match entries with
    | Some e -> e
    | None -> []
  in
  let rec translate_entries (entries: Prog.Table.entry list) =
    match entries with
    | [] ->
       begin match default_action with
       | Some act -> translate_action_ref action_map act
       | None -> C.CBlock []
       end
    | entry::rest ->
       C.CIf (translate_matches (snd entry).matches key,
              translate_action_ref action_map (snd entry).action,
              translate_entries rest)
  in
  translate_entries entries

and translate_apply_call (map: table_map) (obj: Prog.Expression.t) : C.cstmt =
  let func = translate_expr obj in
  let func_name =
    match func with
    | C.CVar s -> s
    | _ -> "fail"
  in
  match (snd obj).typ with
  | Table _ ->
     translate_table_apply map func_name
  | _ -> 
     CMethodCall (func, [])

and translate_stmt (map: table_map) (stmt: Prog.Statement.t) : C.cstmt =
  match (snd stmt).stmt with 
  | MethodCall {func = _, {expr = ExpressionMember {expr = pkt; name = (_, "extract")}; _};
                type_args = [hdr_typ];
                args = [hdr_arg]} ->
    assert_packet_in (snd pkt).typ;
    let width = type_width hdr_typ in
    let hdr_arg = hdr_arg |> translate_arg Out |> cast_to_void_ptr in
    let pkt_arg = translate_expr pkt in
    C.CMethodCall (C.CVar "extract", [pkt_arg; hdr_arg; C.CIntLit width])
  | MethodCall {func = _, {expr = ExpressionMember {expr = pkt; name = (_, "emit")}; _};
                type_args = [hdr_typ];
                args = [hdr_arg]} ->
    assert_packet_out (snd pkt).typ;
    let width = type_width hdr_typ in
    let hdr_arg = hdr_arg |> translate_arg Out |> cast_to_void_ptr in
    let pkt_arg = translate_expr pkt in
    C.CMethodCall (C.CVar "emit", [pkt_arg; hdr_arg; C.CIntLit width])
  | MethodCall {func = _, {expr = ExpressionMember {expr = obj; name = (_, "apply")}; _};
                type_args = [];
                args = []} ->
    translate_apply_call map obj
  | MethodCall { func; type_args; args } -> 
    let args = translate_args args in
    C.CMethodCall (translate_expr func, args)
  | Assignment { lhs; rhs } -> 
    C.CAssign (translate_expr lhs, translate_expr rhs)
  | _ -> failwith "translate_stmt unimplemented"

and translate_stmts map (stmts: Prog.Statement.t list) : C.cstmt list =
  stmts
  |> List.map ~f:(translate_stmt map)

and translate_block map (block: Prog.Block.t) : C.cstmt list =
  (snd block).statements
  |> translate_stmts map

and get_type (typ: Typed.Type.t) : C.ctyp  =
  match typ with
  | Typed.Type.Bool -> C.CBool 
  | Typed.Type.TypeName (BareName n) ->
    C.CTypeName (snd n) 
  | Typed.Type.Bit {width = 8} ->
    C.CBit8
  | _ -> failwith "incomplete"

and translate_key (key : Prog.Table.key) = 
  get_expr_mem_lst (snd key).key

and translate_local_decls (d: Prog.Declaration.t list) : C.cdecl list * C.cstmt list =
  [], []

and translate_decl map (d: Prog.Declaration.t) : table_map * C.cdecl list =
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
    let locals_decls, locals_stmts = translate_local_decls locals in
    let state_stmts = translate_parser_states map states in
    let func_decl = C.CFun (CVoid, snd name, translate_params params, locals_stmts @ state_stmts) in
    map, locals_decls @ [func_decl]
  | Function { return; name; type_params; params; body } ->
    map, [C.CComment "todo: Function"]
  | Action { name; data_params; ctrl_params; body; _ } ->
     let params = translate_params (data_params @ ctrl_params) in
     map, [C.CFun (CVoid, snd name, 
                   params, 
                   translate_block map body)]
  | Control { name; type_params; params; constructor_params; locals; apply; _ } ->
    let params = translate_params (params @ constructor_params) in
    let map', locals = translate_decls map locals in 
    let func_decl = 
      C.CFun (CVoid, snd name, params, 
              translate_block map' apply) in 
    map, locals @ [func_decl]
  | Constant _ ->
    map, [C.CComment "todo: Constant"]
  | Instantiation _ ->
    map, [C.CComment "todo: Instantiation"]
  | Variable _ ->
    map, [C.CComment "todo: Variable"]
  | Table { name; key; actions; entries; default_action; size; custom_properties; _ } ->
    translate_table map (snd name, key, actions, entries, default_action, size, custom_properties)
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

and translate_decls map (decls: Prog.Declaration.t list) : table_map * C.cdecl list =
  let f (map, decls) decl =
    let map, decls' = translate_decl map decl in
    (map, decls @ decls')
  in
  List.fold ~init:(map, []) ~f decls

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

and translate_match ((match_expr, key): Prog.Match.t * Prog.Table.key) : C.cexpr =
  match (snd match_expr).expr with
  | DontCare -> C.CBoolExp true
  | Expression {expr} ->
     begin match (snd key).match_kind with
     | _, "exact" ->
        C.CEq (translate_expr (snd key).key, translate_expr expr)
     | _ -> failwith "match_kind not implemented"
     end

and translate_matches (match_exprs: Prog.Match.t list) (keys: Prog.Table.key list) : C.cexpr =
  List.zip_exn match_exprs keys
  |> List.map ~f:translate_match
  |> List.fold ~init:(C.CBoolExp true) ~f:(fun e1 e2 -> C.CAnd (e1, e2))

and translate_table map (name, keys, actions, entries, default_action, size, custom_properties) = 
  let summary = { key = keys; actions; entries; default_action; size; custom_properties } in
  map |> StrMap.add_exn ~key:name ~data:summary, []

and method_call_table (name : Types.name) = 
  C.CMethodCall (C.CVar (snd (get_name name)), [])

and translate_action_ref action_map (aref : Prog.Table.action_ref) = 
  let aref = (snd aref).action in
  let fixed_args = StrMap.find_exn action_map (aref.name |> get_name |> snd) in
  let entry_args = aref.args in
  let args = translate_args (fixed_args @ entry_args) in
  C.CMethodCall (C.CVar (snd (get_name aref.name)), args)

and get_first (list) = 
  match list with 
  | h::t -> h
  | _ -> failwith "empty"

and translate_parser_locals (locals: Prog.Declaration.t list) : C.cstmt list =
  []

and translate_parser_states map (states: Prog.Parser.state list) : C.cstmt list =
  let add_state idx (map: 'a StrMap.t) (state: Prog.Parser.state) =
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
  C.CCase (CIntLit state_id, stmts @ annot)

and translate_trans (states: int StrMap.t) (t: Prog.Parser.transition) : C.cstmt list =
  match snd t with
  | Direct {next} ->
    let nextid = Map.find_exn states (snd next) in
    [C.CAssign (next_state_var, CIntLit nextid)]
  | Select _ ->
    failwith "translation of select() unimplemented"

and param_to_struct_field (param : Typed.Parameter.t) : C.cfield =
  let ctyp = translate_type param.typ in
  C.CField (ctyp, snd param.variable)

and params_to_struct_fields (params : Typed.Parameter.t list) : C.cfield list =
  params
  |> List.map ~f:param_to_struct_field

and translate_param (param: Typed.Parameter.t) : C.cparam =
  let ctyp = translate_type param.typ in
  C.CParam (ctyp, snd param.variable)

and translate_params (params: Typed.Parameter.t list) : C.cparam list =
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

let translate_prog map ((Program prog): Prog.program) : C.cprog =
  prog
  |> translate_decls map
  |> snd

let compile (prog: Prog.program) : C.cprog =
  CInclude "petr4-runtime.h" ::
  translate_prog StrMap.empty prog
