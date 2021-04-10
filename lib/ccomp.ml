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

let rec get_expr_name (e: Prog.Expression.t) : C.cname =
  match (snd e).expr with
  | ExpressionMember x -> get_expr_name x.expr ^ "." ^ snd x.name 
  | FunctionCall x -> failwith "a"
  | NamelessInstantiation x -> failwith "b"
  | String s -> failwith (snd s)
  | Mask x -> failwith "dsjak"
  | Name n -> begin match n with 
      | BareName str -> snd str 
      | _ -> failwith "unimplemented" end 
  | True ->  "true"
  | False -> "false"
  | Int i -> Bigint.to_string (snd i).value
  | Cast {typ ; expr} -> get_expr_name expr
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
            CAddrOf (CMember (CPointer (CVar "state", get_expr_mem expr), snd name))
          | _ -> failwith "unimplemented!"
        end
    in
    fst::get_expr_opt_lst t  

let translate_expr (map: varmap) (e: Prog.Expression.t) : C.cexpr =
  match (snd e).expr with
  | Name (BareName (_, x)) ->
    varmap_find map x
  | _ -> failwith "incomplete"

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
  | MethodCall {func = _, {expr = ExpressionMember {expr = pkt; name = (_, "emit")}; _};
                type_args = [hdr_typ];
                args} ->
    assert_packet_out (snd pkt).typ;
    let width = type_width hdr_typ in
    let args = get_expr_opt_lst args in
    let pkt_arg = C.(CPointer (CVar "state", "pkt")) in
    C.CMethodCall ("emit", pkt_arg :: args @ [C.CIntLit width])
  | MethodCall {func = _, {expr = ExpressionMember {expr = tbl; name = (_, "apply")}; _};
                type_args = [];
                args = []} ->
    C.CMethodCall (get_expr_name tbl, [C.CString "state"])
  | MethodCall { func; type_args; args } -> 
    let args = get_expr_opt_lst args in
    C.CMethodCall (get_expr_name func, args)
  | Assignment { lhs; rhs } -> 
    let left = C.CPointer ((C.CString "state"), (get_expr_name lhs)) in 
    C.CAssign (left, (get_expr_c rhs)) 
  | _ -> failwith "incomplete"

let translate_stmts map (stmts: Prog.Statement.t list) : C.cstmt list =
  stmts
  |> List.map ~f:translate_stmt

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
  get_expr_name (snd key).key

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
    let state_type_name = snd name ^ "_state" in
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
    (* TO DO - MAKE A FUNCTION THAT DOES THIS CONCAT  *)
    (* TO DO - MORE CONSISTENT NAMES *)
    let state_type_name = snd name ^ "_state" in
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

(* TODO - make a general snd function for all of the instances of the string *)

and translate_local (n: string) (map: varmap) (locals : Prog.Declaration.t) : C.cdecl = 
  match snd locals with 
  | Action { name; data_params; ctrl_params; body; _ } -> 
    C.CFun (CVoid, snd name, 
            [CParam (CTypeName "MyC_state", "*state")], 
            translate_block map body)
  | Table { name; key; actions; entries; default_action; size; custom_properties; _ } ->
    translate_table(snd name, key, actions, entries, default_action, size, custom_properties)
  | _ -> failwith "incomplete"

and find_table_name (locals : Prog.Declaration.t list) : string =
  let f decl = 
    match snd decl with 
    | Prog.Declaration.Table {name;_} -> Some (snd name) 
    | _ -> None
  in List.find_map_exn locals ~f
(* match locals with 
   | [] -> ""
   | h::t -> begin 
    match snd h with 
    | Table { name; key; actions; entries; default_action; size; custom_properties; _ } -> 
      snd name
    | _ -> find_table_name t
   end  *)

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

and get_action_ref (actions : Prog.Table.action_ref list) = 
  match actions with
  | [] -> []
  | h::t -> let n = snd h 
    in  [(n.action).name] @ get_action_ref t
(* List.map ~f:ext_action *)

and get_name (n: P4.name) = 
  match n with 
  | BareName b -> b
  | _ -> failwith "f"

and get_cond_logic (entries : Prog.Table.entry list option) (key : Prog.Table.key) =
  let k = translate_key key in 
  begin match entries with 
    | None -> failwith "n"
    | Some e -> begin match e with 
        | [] -> failwith "f"
        | h::t -> let m = (snd h).matches in
          let equal = begin match m with 
            | [] -> failwith "F"
            | (_, {expr = Prog.Match.Expression {expr}; _})::t -> expr 
            | _ -> failwith "f"
          end in 
          C.CPointer ((C.CString "state"), k ^ "!=" ^ (get_expr_name equal)) 
      end 
  end 

and translate_table(name, k, actions, entries, default_action, size, custom_properties) = 
  let k_new = List.hd k in 
  let k_n = begin match k_new with 
    | None -> failwith "f" 
    | Some f -> f end in 
  let l = get_action_ref actions in 
  let first = match l with 
    | h::t -> h
    | _ -> failwith "mistake" in 
  let second = match l with 
    | h::s::t -> s
    | _ -> failwith "mistake!" in
  C.CFun 
    (CVoid, name, [CParam (CTypeName "MyC_state", "*state")], 
     C.[CIf ((get_cond_logic entries k_n),
             (CMethodCall ((snd (get_name first)), [C.CString "state"])),
             (CMethodCall (snd (get_name  second), [C.CString "state"])))])

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

and translate_fun (map: varmap) (s: Prog.Statement.t) : C.cstmt = 
  match (snd s).stmt with 
  | MethodCall {func = _, {expr = ExpressionMember {expr = pkt; name = (_, "emit")}; _};
                type_args = [hdr_typ];
                args} ->
    assert_packet_out (snd pkt).typ;
    let width = type_width hdr_typ in
    let args = get_expr_opt_lst args in
    let pkt_arg = C.(CPointer (CVar "state", "pkt")) in
    C.CMethodCall ("emit", pkt_arg :: args @ [C.CIntLit width])
  | MethodCall { func; type_args; args } -> 
    let args = get_expr_opt_lst args in
    C.CMethodCall (get_expr_name func, args)
  | Assignment { lhs; rhs } -> 
    let left = C.CPointer ((C.CString "state"), (get_expr_name lhs)) in 
    C.CAssign (left, (get_expr_c rhs)) 
  | _ ->  failwith "incomplete"

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
