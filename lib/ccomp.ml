module Petr4Info = Info
(* open Core  *)
open Core_kernel
module Info = Petr4Info
module C = Csyntax

module StrMap = Map.Make(String)

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

let translate_stmt (stmt: Prog.Statement.t) : C.cstmt =
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
    CMethodCall (translate_expr obj, [])
  | MethodCall { func; type_args; args } -> 
    let args = translate_args args in
    C.CMethodCall (translate_expr func, args)
  | Assignment { lhs; rhs } -> 
    C.CAssign (translate_expr lhs, translate_expr rhs)
  | _ -> failwith "translate_stmt unimplemented"

let translate_stmts (stmts: Prog.Statement.t list) : C.cstmt list =
  stmts
  |> List.map ~f:translate_stmt

let translate_block (block: Prog.Block.t) : C.cstmt list =
  (snd block).statements
  |> translate_stmts

let get_type (typ: Typed.Type.t) : C.ctyp  =
  match typ with
  | Typed.Type.Bool -> C.CBool 
  | Typed.Type.TypeName (BareName n) ->
    C.CTypeName (snd n) 
  | Typed.Type.Bit {width = 8} ->
    C.CBit8
  | _ -> failwith "incomplete"

let translate_key (key : Prog.Table.key) = 
  get_expr_mem_lst (snd key).key

let translate_local_decls (d: Prog.Declaration.t list) : C.cdecl list * C.cstmt list =
  [], []

let rec translate_decl (d: Prog.Declaration.t) : C.cdecl list =
  match snd d with
  | Struct {name; fields; _} ->
    let cfields = translate_fields fields in
    [C.CStruct (snd name, cfields)]
  | Header {name; fields; _} ->
    let cfields = translate_fields fields in
    let valid = C.CField (CBool, "__header_valid") in
    [C.CStruct (snd name, valid :: cfields)]
  | HeaderUnion {name; fields; _} ->
    [C.CComment "todo: Header union"]
  | Enum _
  | SerializableEnum _ ->
    [C.CComment "todo: Enum/SerializableEnum"]
  | Parser { name; type_params; params; constructor_params; locals; states; _} -> 
    let locals_decls, locals_stmts = translate_local_decls locals in
    let state_stmts = translate_parser_states states in
    let func_decl = C.CFun (CVoid, snd name, translate_params params, locals_stmts @ state_stmts) in
    locals_decls @ [func_decl]
  | Function { return; name; type_params; params; body } ->
    [C.CComment "todo: Function"]
  | Action { name; data_params; ctrl_params; body; _ } ->
     let params = translate_params (data_params @ ctrl_params) in
     [C.CFun (CVoid, snd name, 
                   params, 
                   translate_block body)]
  | Control { name; type_params; params; constructor_params; locals; apply; _ } ->
    let params = translate_params (params @ constructor_params) in
    let locals = translate_decls locals in 
    let func_decl = 
      C.CFun (CVoid, snd name, params, 
              translate_block apply) in 
    locals @ [func_decl]
  | Constant _ ->
    [C.CComment "todo: Constant"]
  | Instantiation _ ->
    [C.CComment "todo: Instantiation"]
  | Variable _ ->
    [C.CComment "todo: Variable"]
  | Table { name; key; actions; entries; default_action; size; custom_properties; _ } ->
    translate_table (snd name, key, actions, entries, default_action, size, custom_properties)
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
    []

and translate_decls (decls: Prog.Declaration.t list) : C.cdecl list =
  decls
  |> List.concat_map ~f:translate_decl

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

and get_name (n: Types.name) = 
  match n with 
  | BareName b -> b
  | _ -> failwith "faa"

(* todo: keylist instead of key *)
and get_cond_logic (entries : Prog.Table.entry list option) (key_name: C.cname) =
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
        C.CEq (C.CVar key_name, translate_expr equal)
    end 

and get_entry_methods (entries : Prog.Table.entry list option) =
  match entries with 
  | None -> failwith "n"
  | Some e -> 
    let rec get_entry_methods_internal (lst : Prog.Table.entry list) = match lst with 
      | [] -> []
      | h::t -> [((snd h).action)] @ get_entry_methods_internal t  in
    let l = get_entry_methods_internal e in 
    get_action_ref l 

and translate_inner ((key_name : C.cname), (entries : Prog.Table.entry list option), (default_action : Prog.Table.action_ref option)) : C.cstmt = 
  (* todo - deal with multiple keys  *)
  (* todo - ternary matches in entries - spec value and bit mask (e.g. or with a mask), prefix matches  *)
  match entries with 
  | None -> failwith "f"
  | Some s ->
     begin match s with 
     | [] -> method_call_table (get_default_action default_action)
     | h::t -> C.CIf (get_cond_logic entries key_name,
                      method_call_table_entry h,
                      translate_inner (key_name, Some t, default_action)) 
     end 

and translate_table (name, keys, actions, entries, default_action, size, custom_properties) = 
  let key_name = "key" in
  let key_param =
    match keys with
    | [key] ->
       let t = translate_type (snd (snd key).key).typ in
       C.CParam (t, key_name)
    | _ -> failwith "expect tables to have a single key"
  in
  [C.CFun (C.CVoid, name, [key_param], [translate_inner (key_name, entries, default_action)])]

and method_call_table (name : Types.name) = 
  C.CMethodCall (C.CVar (snd (get_name name)), [])

and method_call_table_entry (entry : Prog.Table.entry) = 
  let n = snd (snd entry).action in 
  C.CMethodCall (C.CVar (snd (get_name (n.action).name)), [])

and get_first (list) = 
  match list with 
  | h::t -> h
  | _ -> failwith "empty"

and translate_parser_locals (locals: Prog.Declaration.t list) : C.cstmt list =
  []

and translate_parser_states (states: Prog.Parser.state list) : C.cstmt list =
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

let translate_prog ((Program prog): Prog.program) : C.cprog =
  prog
  |> translate_decls

let compile (prog: Prog.program) : C.cprog =
  CInclude "petr4-runtime.h" ::
  translate_prog prog
