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

let rec get_expr_name (e: Prog.Expression.t) : C.cname =
  match (snd e).expr with
  | ExpressionMember x -> get_expr_name x.expr ^ "." ^ snd x.name 
  | Name n -> begin match n with 
      | BareName str -> snd str 
      | _ -> failwith "unimplemented" end 
  | True ->  "true"
  | False -> "false"
  | Int i -> Bigint.to_string (snd i).value
  | Cast {typ ; expr} -> get_expr_name expr
  | _ -> failwith "unimplemented"

let get_name (n: Types.name) = 
  match n with 
  | BareName b -> b
  | _ -> failwith "faa"

let translate_type (typ: Typed.Type.t) : C.ctyp =
  match typ with
  | Typed.Type.Bool -> C.CBool
  | Typed.Type.TypeName (BareName n) ->
    C.CTypeName (snd n)
  | Typed.Type.Bit {width = 8} ->
    C.CBit8
  | _ -> failwith "incomplete"

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
  | List {values} -> CList (List.map ~f:translate_expr values)
  | DontCare -> failwith "match statement not implemented yet"
  | UnaryOp {op; arg} -> begin match snd op with  
      | Not -> CUOpNot (translate_expr arg)
      | BitNot -> CUOpBitNot (translate_expr arg)
      | UMinus -> CUOpUMinus (translate_expr arg)
    end 
  | FunctionCall {func; type_args; args} -> 
    let rec get_args (a : Prog.Expression.t option list) = 
      match a with 
      | [] -> []
      | (Some h)::t -> translate_expr h::get_args t 
      | None::t -> get_args t in
    CCall ((get_expr_name func), get_args args)
  | BinaryOp {op; args} -> CBinOp (op, translate_expr (fst args), translate_expr (snd args))
  | TypeMember {typ; name} -> CMember (CVar (typ |> get_name |> snd), snd name)
  | ErrorMember e -> Cerr (snd e)
  | Ternary t -> CTernary (translate_expr t.cond, translate_expr t.tru, translate_expr t.fls)
  | ArrayAccess x -> CArrayAccess (translate_expr x.array, translate_expr x.index)
  | BitStringAccess x -> CBitStringAccess (translate_expr x.bits, x.lo, x.hi)
  | Mask x -> CBinOp ((Info.dummy, Types.Op.And), translate_expr x.expr, translate_expr x.mask)
  | NamelessInstantiation x -> failwith "f"
  | Record r -> failwith "f" (** use struct literals *)
  | Range r -> failwith "f"

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

let rec get_expr_c (e: Prog.Expression.t) : C.cexpr =
  (* todo: expand get_expr_c  *)
  match (snd e).expr with
  | Name n -> begin match n with 
      | BareName str -> CString (snd str) 
      | _ -> failwith "unimplemented" end 
  | True ->  CBoolExp true  
  | False -> CBoolExp false  
  | Int i -> CIntLit (Bigint.to_int_exn (snd i).value)
  | Cast c -> get_expr_c c.expr
  | _ -> failwith (Prog.Expression.show e )

and build_action_map actions =
  let f map (act: Prog.Table.action_ref) =
    let act = (snd act).action in
    map
    |> StrMap.add_exn ~key:(act.name |> get_name |> snd) ~data:act.args
  in
  List.fold ~f ~init:StrMap.empty actions

and translate_table_apply map tbl_name default_args =
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
        | Some act -> translate_action_ref action_map act default_args
        | None -> C.CBlock []
      end
    | entry::rest ->
      C.CIf (translate_matches (snd entry).matches key,
             translate_action_ref action_map (snd entry).action default_args,
             translate_entries rest)
  in
  translate_entries entries

and translate_apply_call (map: table_map) (obj: Prog.Expression.t) default_args : C.cstmt =
  let func = translate_expr obj in
  let func_name =
    match func with
    | C.CVar s -> s
    | _ -> "fail"
  in
  match (snd obj).typ with
  | Table _ ->
    translate_table_apply map func_name default_args
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
    translate_apply_call map obj []
  | MethodCall { func; type_args; args } -> 
    let args = translate_args args in
    C.CMethodCall (translate_expr func, args)
  | Assignment { lhs; rhs } -> 
    C.CAssign (translate_expr lhs, translate_expr rhs)
  | _ -> failwith "translate_stmt unimplemented"

and translate_stmts map (stmts: Prog.Statement.t list) : C.cstmt list =
  stmts
  |> List.map ~f:(translate_stmt map)

(* just like the translate_decl change. I'm adding two new methods for statements
  inside a control block. *)
and translate_control_local_stmt (map: table_map) (default_args: C.cexpr list) (stmt: Prog.Statement.t) : C.cstmt =
  match (snd stmt).stmt with
  | MethodCall {func = _, {expr = ExpressionMember {expr = obj; name = (_, "apply")}; _};
                type_args = [];
                args = []} ->
    translate_apply_call map obj default_args
  | _ -> translate_stmt map stmt


and translate_control_local_stmts map default_args (stmts: Prog.Statement.t list) : C.cstmt list =
  stmts
  |> List.map ~f:(translate_control_local_stmt map default_args)

and translate_block map (block: Prog.Block.t) : C.cstmt list =
  (snd block).statements
  |> translate_stmts map

and translate_control_local_block map (block: Prog.Block.t) default_args: C.cstmt list = 
  (snd block).statements
  |> translate_control_local_stmts map default_args

(* The signature matters here. We want to ensure that the params and args have
same order. And the safest way to do it is just to do it after the translation
to C.cparam *)
and args_of_params (params: C.cparam list) : C.cexpr list = 
  List.map ~f:C.arg_of_param params

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
(* I think the intention of this function is similar to what I write below, but
I don't see how you can carry over the parameters without it as an argument.
thus I will write a new one below *)
and translate_local_decls (d: Prog.Declaration.t list) : C.cdecl list * C.cstmt list =
  [], []

and translate_decl map (d: Prog.Declaration.t): table_map * C.cdecl list =
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
    let map', locals = translate_control_local_decls map locals params in 
    let func_decl = 
      C.CFun (CVoid, snd name, params, 
              translate_control_local_block map' apply (args_of_params params)) in 
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

(* the thing that confuses me a lot is the naming of Action's params. 
I thought that the ctrl_params are exactly the parameters from the control block
containing it. However, the ctrl_params were more like the constructor params
where they just don't have any direction. I was tempted to change the generation
of the ctrl_params, but I eventually decided to modify it in this pass. *)
and translate_control_local_decl map (d: Prog.Declaration.t) (control_params: C.cparam list): table_map * C.cdecl list =
  match snd d with
  (* Action is the only one I changed for now. But we might need to do
  something different with other local declarations as well. *)
  | Action { name; data_params; ctrl_params; body; _ } ->
    let params = control_params @ (translate_params (data_params @ ctrl_params)) in
    map, [C.CFun (CVoid, snd name, 
                  params, 
                  translate_block map body)]
  | _ -> translate_decl map d

and translate_control_local_decls map (decls: Prog.Declaration.t list) (control_params: C.cparam list): table_map * C.cdecl list =
  let f (map, decls) decl =
    let map, decls' = translate_control_local_decl map decl control_params in
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
        C.CBinOp ((Info.dummy, Types.Op.Eq), translate_expr (snd key).key, translate_expr expr)
      | _ -> failwith "match_kind not implemented"
    end

and translate_matches (match_exprs: Prog.Match.t list) (keys: Prog.Table.key list) : C.cexpr =
  List.zip_exn match_exprs keys
  |> List.map ~f:translate_match
  |> List.fold ~init:(C.CBoolExp true) ~f:(fun e1 e2 -> C.CBinOp ((Info.dummy, Types.Op.Eq), e1, e2))

  (* Including a list of default arguments into this. However, I'm really not sure what is the action map's
  fixed_args for. Hopefully this is not duplicate work *)
and translate_action_ref action_map (aref : Prog.Table.action_ref) (default : C.cexpr list)= 
  let aref = (snd aref).action in
  (* this is the confusing part *)
  let fixed_args = StrMap.find_exn action_map (aref.name |> get_name |> snd) in
  let entry_args = aref.args in
  (* Note the order here: control arguments go first *)
  let args = default @ (translate_args (fixed_args @ entry_args)) in
  C.CMethodCall (C.CVar (snd (get_name aref.name)), args)

  and get_default_action (action : Prog.Table.action_ref option) = 
  match action with
  | None -> failwith "unimplemented"
  | Some h -> ((snd h).action).name

and get_action_ref (actions : Prog.Table.action_ref list) = 
  match actions with
  | [] -> []
  | h::t -> let n = snd h 
    in  [(n.action).name] @ get_action_ref t

and get_cond_logic (entry : Prog.Table.entry) (keys : Prog.Table.key list) =
  let m = (snd entry).matches in
  let init = C.CBoolExp true in 
  let f (acc:C.cexpr) (k:Prog.Table.key) (m_el:Prog.Match.t) = 
    begin match (snd m_el).expr with 
      | DontCare -> acc  
      | Expression {expr} -> C.CBinOp ((Info.dummy, Types.Op.Eq), translate_pointer (C.CString "state") k, get_expr_c expr) 
    end in 
  List.fold2_exn keys m ~init ~f 

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
  match entries with 
  | None -> failwith "f"
  | Some s -> 
    let s_rev = List.rev s in 
    let f (acc: C.cstmt) (h : Prog.Table.entry) = 
      C.CIf (get_cond_logic h k, method_call_table_entry h, acc) in 
    List.fold s_rev ~init:(method_call_table (get_default_action default_action)) ~f 

and translate_table map (name, keys, actions, entries, default_action, size, custom_properties) = 
  let summary = { key = keys; actions; entries; default_action; size; custom_properties } in
  map |> StrMap.add_exn ~key:name ~data:summary, []

and method_call_table (name : Types.name) = 
  C.CMethodCall (C.CVar (snd (get_name name)), [])

(* and translate_table(control_name, name, k, actions, entries, default_action, size, custom_properties) = 
   let state_type = C.(CPtr (CTypeName (make_state_name control_name))) in
   let state_param = C.CParam (state_type, "state") in
   C.CFun(C.CVoid, name, [state_param], [translate_inner (k, entries, default_action)])  *)

and method_call_table_entry (entry : Prog.Table.entry) = 
  let n = snd (snd entry).action in 
  C.CMethodCall (C.CString(snd (get_name (n.action).name)), [C.CString "state"])

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
     CWhile (C.CBinOp ((Info.dummy, Types.Op.Ge), next_state_var, CIntLit 0),
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

let translate_prog map ((Program prog): Prog.program) : C.cprog =
  prog
  |> translate_decls map
  |> snd

let compile (prog: Prog.program) : C.cprog =
  CInclude "petr4-runtime.h" ::
  translate_prog StrMap.empty prog
