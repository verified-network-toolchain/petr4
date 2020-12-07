module I = Info
open Core_kernel
open Prog
open Eval_env
open Typed
open Target
open Bitstring
open Util
module Info = I (* JNF: ugly hack *)

let (>>|) v f = Option.map ~f:f v

type env = Eval_env.t

module type Interpreter = sig

  type state

  val empty_state : state

  val eval_expression : env -> state -> coq_Expression -> (state * coq_Value)

  val eval_statement : ctrl -> env -> state -> coq_Statement -> (env * state)

  val eval_declaration : ctrl -> env -> state -> coq_Declaration -> (env * state)

  val eval_program : ctrl -> env -> state -> buf -> Bigint.t -> program ->
    state * (buf * Bigint.t) option
end

module MakeInterpreter (T : Target) = struct

  type state = T.state

  let empty_state = State.empty

  let assign_lvalue = assign_lvalue T.read_header_field T.write_header_field

  let value_of_lvalue = value_of_lvalue T.read_header_field

  (*----------------------------------------------------------------------------*)
  (* Declaration Evaluation *)
  (*----------------------------------------------------------------------------*)

  let rec eval_declaration (ctrl : ctrl) (env : env) (st : state)
      (d : coq_Declaration) : env * state =
    match d with
    | DeclConstant (_, typ, MkP4String (_, name), value) ->
      eval_const_decl ctrl env st typ value name
    | DeclInstantiation (_, typ, args, MkP4String (_, name), None) ->
      eval_instantiation ctrl env st typ args name
    | DeclInstantiation (_, _, _, _, Some _) ->
      failwith "abstract externs unsupported"
    | DeclParser (_, MkP4String (_, name), _, params, constructor_params, locals, states) ->
      eval_parser_decl env st name constructor_params params locals states
    | DeclControl (_, MkP4String (_, name), _, params, constructor_params, locals, apply) ->
      eval_control_decl env st name constructor_params params locals apply
    | DeclFunction (_, _, MkP4String (_, name), _, params, body) ->
      eval_fun_decl env st name params body
    | DeclExternFunction (_, _, MkP4String (_, name), _, params) ->
      eval_extern_fun env st name params
    | DeclVariable (_, typ, MkP4String (_, name), init) ->
      let (a,b,_) = eval_var_decl ctrl env st typ name init in (a,b)
    | DeclValueSet (_, typ, size, name) ->
      let (a,b,_) = eval_set_decl ctrl env st typ name size in (a,b)
    | DeclAction (_, MkP4String (_, name), data_params, ctrl_params, body) ->
      eval_action_decl env st name data_params ctrl_params body
    | DeclTable (_, MkP4String (_, name), key, actions, entries, default_action, size, custom_properties) ->
      eval_table_decl ctrl env st name key actions entries default_action size custom_properties
    | DeclSerializableEnum (_, _, MkP4String (_, name), members) ->
      eval_senum_decl env st name members
    | DeclExternObject (_, MkP4String (_, name), type_params, methods) ->
      eval_extern_obj env st name methods
    | DeclPackageType (_, MkP4String (_,n), _, params) ->
      eval_pkgtyp_decl env st n params
    | _ -> env, st

  and eval_const_decl (ctrl : ctrl) (env : env) (st : state) (typ : coq_P4Type)
      (v : coq_ValueBase) (name : string) : env * state =
    let l = State.fresh_loc () in
    let st = State.insert_heap l (ValBase v) st in
    Eval_env.insert_val_bare name l env, st

  and eval_instantiation (ctrl : ctrl) (env : env) (st : state) (typ : coq_P4Type)
      (args : coq_Expression list) (name : string) : env * state =
    let env' = Eval_env.set_namespace (Eval_env.get_namespace env ^ name) env in
    let (st',_,obj) = eval_nameless env' st typ args in
    let env' = Eval_env.set_namespace (Eval_env.get_namespace env) env in
    let l = State.fresh_loc () in
    let st' = State.insert_heap l obj st' in
    (Eval_env.insert_val_bare name l env', st')

  and eval_parser_decl (env : env) (st : state) (name : string)
      (constructor_params : coq_P4Parameter list) (params : coq_P4Parameter list)
      (locals : coq_Declaration list) (states : coq_ParserState list) : env * state =
    let v: coq_ValueObject =
      ValObjParser (env,
                    constructor_params,
                    params,
                    locals,
                    states)
    in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in 
    let env = Eval_env.insert_val_bare name l env in
    env, st

  and eval_control_decl (env : env) (st : state) (name : string)
      (constructor_params : coq_P4Parameter list) (params : coq_P4Parameter list)
      (locals : coq_Declaration list) (apply : coq_Block) : env * state =
    let v = VControl {
      cscope = env;
      cconstructor_params = constructor_params;
      cparams = params;
      clocals = locals;
      apply = apply;
    } in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    let env = Eval_env.insert_val_bare name l env in
    env, st

  and eval_fun_decl (env : env) (st : state) (name : string)
      (params : coq_P4Parameter list) (body : coq_Block) : env * state =
    let l = State.fresh_loc () in
    let st = State.insert_heap l (VFun{scope=env;params;body}) st in
    Eval_env.insert_val_bare name l env, st

  and eval_extern_fun (env : env) (st : state) (name : string)
      (params : coq_P4Parameter list) : env * state =
    let l = State.fresh_loc () in
    let st = State.insert_heap l (VExternFun {name; caller = None; params;}) st in
    Eval_env.insert_val_bare name l env, st

  and eval_var_decl (ctrl : ctrl) (env : env) (st : state) (typ : coq_P4Type)
      (name : string) (init : coq_Expression option) : env * state * signal =
    let init_val = init_val_of_typ env typ in
    let l = State.fresh_loc () in
    let st = State.insert_heap l init_val st in
    match init with
    | None ->
      let env = Eval_env.insert_val_bare name l env in
      env, st, SContinue
    | Some e ->
      let st, signal, init_val = eval_expr env st SContinue e in
      match signal with
      | SContinue ->
         let st = State.insert_heap l init_val st in
         Eval_env.insert_val_bare name l env, st, SContinue
      | signal -> env, st, signal

  and eval_set_decl (ctrl : ctrl) (env : env) (st : state) (typ : coq_P4Type)
      (name : string) (size : coq_Expression) : env * state * signal =
    let env = Eval_env.insert_typ_bare name typ env in
    let (st, s, size') = eval_expr env st SContinue size in
    let size'' = assert_rawint size' in
    match s with
    | SContinue ->
      let ms = snd ctrl in
      if Bigint.(Bigint.of_int (List.length ms) > size'')
      then failwith "too many elements inserted to value set"
      else
        let vset = VSet (SValueSet{size=size';members=ms;sets=[]}) in
        let l = State.fresh_loc () in
        let st = State.insert_heap l vset st in
        let env = Eval_env.insert_val_bare name l env in
        (env, st, s)
    | SReject _ -> (env, st, s)
    | _ -> failwith "value set declaration should not return or exit"

  and eval_action_decl (env : env) (st : state) (name : string)
      (data_params : coq_P4Parameter list) (ctrl_params : coq_P4Parameter list)
      (body : coq_Block) : env * state =
    let l = State.fresh_loc () in
    let st = State.insert_heap l
      (VAction{scope=env; params = data_params @ ctrl_params; body}) st in
    Eval_env.insert_val_bare name l env, st

  and eval_table_decl (ctrl : ctrl) (env : env) (st : state) (name : string)
      (key : Table.key list) (actions : coq_TableActionRef list)
      (entries : (Table.entry list) option) (default : coq_TableActionRef option)
      (size : P4Int.t option) (props : Table.property list) : env * state =
    let pre_ks = key |> List.map ~f:snd in
    let ctrl_entries = match List.Assoc.find (fst (fst ctrl)) name ~equal:String.(=) with
                       | None -> []
                       | Some entries -> create_pre_entries env st actions key entries in
    let entries' = match entries with
                        | None -> ctrl_entries
                        | Some entries -> entries |> List.map ~f:snd in
    let final_entries = sort_priority ctrl env st entries' in
    let ctrl_default = match List.Assoc.find (snd (fst ctrl)) name ~equal:String.(=) with
                       | None -> default
                       | Some actions' -> Some (convert_action env st   actions (List.hd_exn actions')) in
    let v = VTable { name = name;
                    keys = pre_ks;
                    actions = actions;
                    default_action = default_of_defaults ctrl_default;
                    const_entries = final_entries; } in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    (Eval_env.insert_val_bare name l env, st)

  and eval_senum_decl (env : env) (st : state) (name : string)
      (ms : (P4String.t * coq_Expression) list) : env * state =
    let ((st,_),es) = List.fold_map ms ~init:(st,SContinue)
      ~f:(fun (st,s) (n,e) -> let (st,s,v) = eval_expr env st s e in (st,s), (snd n,v)) in
    let v = VSenum es in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    Eval_env.insert_val_bare name l env, st

  and eval_extern_obj (env : env) (st : state) (name : string)
      (methods : MethodPrototype.t list) : env * state =
    let v = let open MethodPrototype in methods
      |> List.map ~f:snd
      |> List.map ~f:(function Constructor {name; params;_}
          | AbstractMethod {name; params; _}
          | Method {name; params; _} -> snd name, params ) in
    let l = State.fresh_loc () in
    let st = State.insert_heap l (VExternObj v) st in
    let env = Eval_env.insert_val_bare name l env in
    env, st

  and eval_pkgtyp_decl (env : env) (st : state) (name : string)
      (params : coq_P4Parameter list) : env * state =
    let v = VPackage {params; args = []} in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    Eval_env.insert_val_bare name l env, st

  (* -------------------------------------------------------------------------- *)
  (* Table Declaration Evaluation *)
  (* -------------------------------------------------------------------------- *)

  and default_of_defaults (p : coq_TableActionRef option) : coq_TableActionRef =
    match p with
    | None ->
      MkTableActionRef
        (Info.dummy,
         MkTablePreActionRef ([], BareName (Info.dummy, "NoAction"), []),
         TypAction ([], []))
      | Some action -> action

  and match_params_to_args (params : coq_P4Parameter list) args : (Ast.number * coq_P4Type) option list =
    match params with
    | p :: params ->
      let right_arg (name, value) =
        if String.(snd p.variable = name)
        then Some (value, p.typ)
        else None
      in
      let maybe_arg_for_p, other_args =
        Util.find_map_and_drop ~f:right_arg args
      in
      begin match maybe_arg_for_p with
      | Some arg_for_p ->
          Some arg_for_p :: match_params_to_args params other_args
      | None -> match_params_to_args params other_args (* arg should already be supplied *)
      end
    | [] ->
      match args with
      | [] -> []
      | a :: rest -> failwith "too many arguments supplied"
  
  and convert_expression (env : env) (s : (Ast.number * coq_P4Type) option) : coq_Expression option =
    let replace_wildcard s =
      String.map s ~f:(fun c -> if Char.(c = '*') then '0' else c) in
    match s with
    | None -> None
    | Some (s, t) ->
      let num = s |> replace_wildcard |> int_of_string |> Bigint.of_int in
      let rec pre_expr_of_typ env (t : coq_P4Type) =
        match t with
        | Integer -> Expression.Int (Info.dummy, {value = num; width_signed = None})
        | Int {width} -> Expression.Int (Info.dummy, {value = num; width_signed = Some (width,true)})
        | Bit {width} -> Expression.Int (Info.dummy, {value = num; width_signed = Some (width,false)})
        | Bool -> Expression.Int (Info.dummy, {value = num; width_signed = None})
        | TypeName n -> pre_expr_of_typ env (Eval_env.find_typ n env)
        | _ -> failwith "unsupported type" in
      let pre_exp = pre_expr_of_typ env t in
      let typed_exp : coq_Expressionyped_t = {expr = pre_exp; typ = t; dir = Directionless} in
      let exp = (Info.dummy, typed_exp) in
      if String.contains s '*'
      then begin
      let pre_exp' = Expression.Mask {expr = exp; mask = exp} in
      let typed_exp' : coq_Expressionyped_t = {expr = pre_exp'; typ = Void; dir = Directionless} in
      Some (Info.dummy, typed_exp') end
      else Some exp
  
  and convert_action env st actions (name, args) =
      let action_name' = Types.BareName (Info.dummy, name) in
      let action_type = Eval_env.find_val action_name' env in
      let type_params = match action_type |> extract_from_state st with
        | VAction {params;_} -> params
        | _ -> failwith "not an action type" in
      let existing_args = List.fold_left actions
                          ~f:(fun acc a -> if Types.name_eq (snd a).action.name action_name'
                                           then (snd a).action.args
                                           else acc)
                          ~init:[] in
      let ctrl_args = match_params_to_args type_params args |> List.map ~f:(convert_expression env) in
      let pre_action_ref : Table.pre_action_ref =
        { annotations = [];
          name = action_name';
          args = existing_args @ ctrl_args } in
      let action : Table.typed_action_ref = { action = pre_action_ref; typ = Void } in (*type is a hack*)
      (Info.dummy, action)

  and create_pre_entries env st actions key add =
    let convert_match ((name, (num_or_lpm : Ast.number_or_lpm)), t) : Match.t =
      match num_or_lpm with
      | Num s ->
        let e = match convert_expression env (Some (s, t)) with
                | Some e -> e
                | None -> failwith "unreachable" in
        let pre_match = Match.Expression {expr = e} in
        let typed_match : Match.typed_t = {expr = pre_match; typ = Integer} in
        (Info.dummy, typed_match)
      | Slash (s, mask) ->
        let expr = match convert_expression env (Some (s, t)) with
                | Some e -> e
                | None -> failwith "unreachable" in
        let mask = match convert_expression env (Some (mask, t)) with
                | Some e -> e
                | None -> failwith "unreachable" in
        let typed_mask : coq_Expressionyped_t =
            { expr = Expression.Mask {expr; mask};
              typ = Typed.Type.Set Typed.Type.Integer;
              dir = Directionless }
        in
        let match_ = Match.Expression {expr = Info.dummy, typed_mask} in
        let typed_match : Match.typed_t = {expr = match_; typ = Integer} in
        (Info.dummy, typed_match)
    in
    let convert_pre_entry (priority, match_list, (action_name, args), id) : Table.pre_entry =
      let key_types = List.map key ~f:(fun k -> (snd (snd k).key).typ ) in
      { annotations = [];
        matches = List.map (List.zip_exn match_list key_types) ~f:convert_match;
        action = convert_action env st actions (action_name, args) } in
    List.map add ~f:convert_pre_entry

  and sort_priority (ctrl : ctrl) (env : env) (st : state)
    (entries : Table.pre_entry list) : coq_TableEntry list =
    let priority_cmp (entry1 : Table.pre_entry) (entry2 : Table.pre_entry) =
      let ann1 = List.find_exn entry1.annotations ~f:(fun a -> String.((snd a).name |> snd = "priority")) in
      let ann2 = List.find_exn entry2.annotations ~f:(fun a -> String.((snd a).name |> snd = "priority")) in
      let body1 = (snd ann1).body |> snd in
      let body2 = (snd ann2).body |> snd in
      match body1,body2 with
      | Unparsed [s1], Unparsed [s2] ->
        let n1 = s1 |> snd |> int_of_string in
        let n2 = s2 |> snd |> int_of_string in
        if n1 = n2 then 0 else if n1 < n2 then -1 else 1
      | _ -> failwith "wrong bodies for @priority" in
    let (priority, no_priority) = List.partition_tf entries ~f:(fun e -> List.exists ~f:(fun a -> String.((snd a).name |> snd = "priority")) e.annotations) in
    let sorted_priority = List.stable_sort priority ~compare:priority_cmp in
    sorted_priority @ no_priority

  (*----------------------------------------------------------------------------*)
  (* Statement Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_stmt (ctrl : ctrl) (env : env) (st : state) (sign : signal)
      (stm : coq_Statement) : (env * state * signal) =
    match (snd stm).stmt with
    | MethodCall{func;type_args;args} -> eval_method_call ctrl env st sign func type_args args
    | Assignment{lhs;rhs}             -> eval_assign ctrl env st sign lhs rhs
    | DirectApplication{typ;args}     -> eval_app' ctrl env st sign args typ
    | Conditional{cond;tru;fls}       -> eval_cond ctrl env st sign cond tru fls
    | BlockStatement{block}           -> eval_block ctrl env st sign block
    | Exit                            -> eval_exit env st sign
    | EmptyStatement                  -> (env, st, sign)
    | Return{expr}                    -> eval_return ctrl env st sign expr
    | Switch{expr;cases}              -> eval_switch ctrl env st sign expr cases
    | DeclarationStatement {decl}     -> eval_declaration_stm ctrl env st sign decl

  and eval_method_call (ctrl : ctrl) (env : env) (st : state) (sign : signal)
      (func : coq_Expression) (targs : coq_P4Type list)
      (args : coq_Expression option list) : env * state * signal =
    match sign with
    | SContinue -> let (s,i,_) = eval_funcall ctrl env st func targs args in (env,s,i)
    | SReject _ | SReturn _ | SExit -> env, st, sign

  and eval_assign (ctrl : ctrl) (env : env) (st : state) (s : signal) (lhs : coq_Expression)
      (rhs : coq_Expression) : env * state * signal =
    match s with
    | SContinue ->
      let (st, s', v) = eval_expr env st SContinue rhs in
      let (st, s'', lv) = lvalue_of_expr env st s lhs in
      begin match s',s'', lv with
        | SContinue, SContinue, Some lv -> let (st, s) = assign_lvalue st env lv v in env, st, s
        | SContinue, _, _               -> env, st, s''
        | _, _, _                       -> env, st, s'
      end
    | SReject _
    | SReturn _
    | SExit     -> (env, st, s)

  and eval_app (ctrl : ctrl) (env : env) (st : state) (s : signal) (v : coq_Value)
    (args : coq_Expression option list) : state * signal * coq_Value =
    match s with
    | SContinue ->
      begin match v with
        | VParser {pscope;pparams;plocals;states;_} ->
          let (s, st') = eval_parser ctrl env st pparams args pscope plocals states in
          (s, st', VNull)
        | VControl {cscope;cparams;clocals;apply;_} ->
          let (st,s) = eval_control ctrl env st cparams args cscope clocals apply in
          (st,s,VNull)
        | VTable {keys;const_entries;name;actions;default_action} ->
          eval_table ctrl env st keys const_entries name actions default_action
        | _ -> failwith "apply not implemented on type" end
    | SReject _ | SReturn _ | SExit -> (st, s, VNull)

  and eval_table (ctrl : ctrl) (env : env) (st : state) (key : Table.pre_key list)
      (entries : Table.pre_entry list)
      (name : string) (actions : coq_TableActionRef list)
      (default : coq_TableActionRef) : state * signal * coq_Value =
    let ks = key |> List.map ~f:(fun k -> k.key) in
    let mks = key |> List.map ~f:(fun k -> k.match_kind |> snd) in
    let ((st',s), ks') = List.fold_map ks ~init:(st, SContinue)
        ~f:(fun (b, c) k ->
            let x,y,z = eval_expr env b c k in ((x,y),z)) in
    let f ((v,w,x,y),z) = ((v,w,x),(y,z)) in
    let sort_mks = check_lpm_count mks in
    let ws = List.map ks' ~f:(width_of_val) in
    let ((env, st'', s'),entries') =
      List.fold_map entries ~init:(env,st',s)
        ~f:(fun (a,b,c) d -> (set_of_matches ctrl a b c d.matches ws, d.action) |> f) in
    let (entries'', ks'') = if List.equal String.equal mks ["lpm"] then (sort_lpm entries', ks')
      else if sort_mks then filter_lpm_prod st env mks ks' entries'
      else (entries', ks') in
    let l = List.filter entries'' ~f:(fun (s,a) -> values_match_set st ks'' s) in
    let action = match l with
                | [] -> default
                | _ -> List.hd_exn l |> snd in
    let action_name = Table.((snd action).action.name) in
    let action_value = Eval_env.find_val action_name env |> extract_from_state st'' in
    let args = Table.((snd action).action.args) in
    match action_value with
    | VAction{scope;params;body}  ->
      let (st''',s,_) = eval_funcall' env st'' scope params args body in
      let hit_bool = VBool (not (List.is_empty l)) in
      let miss_bool = VBool (List.is_empty l) in
      let run_enum = VEnumField{typ_name=name; enum_name=name_only action_name} in
      let v = VStruct {fields=[
                            ("hit", hit_bool);
                            ("miss", miss_bool);
                            ("action_run", run_enum)
                          ]} in
      (st''',s,v)
    | _ -> failwith "table expects an action"

  and filter_lpm_prod (st : state) (env : env) (mks : string list) (ks : coq_Value list)
      (entries : (coq_ValueSet * coq_TableActionRef) list)
      : (coq_ValueSet * coq_TableActionRef) list * (coq_Value list) =
    let index = match List.findi mks ~f:(fun _ s -> String.equal s "lpm") with
      | None -> failwith "unreachable, should have lpm"
      | Some (i,_) -> i in
    let f = function
      | SProd l, a -> (List.nth_exn l index, a)
      | _ -> failwith "not lpm prod" in
    let entries =
      entries
      |> List.filter ~f:(fun (s,a) -> values_match_set st ks s)
      |> List.map ~f:f in
    let ks' = [List.nth_exn ks index] in
    (sort_lpm entries, ks')

  and check_lpm_count (mks : string list) : bool =
    let num_lpm =
      mks
      |> List.filter ~f:(fun s -> String.equal s "lpm")
      |> List.length in
    if num_lpm > 1
    then failwith "more than one lpm"
    else num_lpm = 1

  and sort_lpm (entries : (coq_ValueSet * coq_TableActionRef) list)
      : (coq_ValueSet * coq_TableActionRef) list =
    let entries' = List.map entries ~f:(fun (x,y) -> lpm_set_of_set x, y) in
    let (entries'', uni) =
      match List.findi entries' ~f:(fun i (s,_) -> Poly.(s = SUniversal)) with
      | None -> (entries', None)
      | Some (i,_) ->
        let es = List.filteri entries' ~f:(fun ind _ -> ind < i) in
        let u = List.nth_exn entries' i in
        (es, Some u) in
    let compare (s1,_) (s2,_) =
      let (_,n1,_) = assert_lpm s1 in
      let (_,n2,_) = assert_lpm s2 in
      if Bigint.(n1 = n2) then 0
      else if Bigint.(n1 > n2) then -1
      else 1 in
    let sorted = List.sort entries'' ~compare:compare in
    match uni with
    | None -> sorted
    | Some u -> sorted @ [u]

  and lpm_set_of_set (s : coq_ValueSet) : coq_ValueSet =
    match s with
    | SSingleton{w;v} ->
      let v' = bitwise_neg_of_bigint Bigint.zero w in
      SLpm{w=VBit{w;v};nbits=w;v=VBit{w;v=v'}}
    | SMask{v=v1;mask=v2} ->
      SLpm{w=v1;nbits=v2 |> bigint_of_val |> bits_of_lpmmask Bigint.zero false;v=v2}
    | SProd l -> List.map l ~f:lpm_set_of_set |> SProd
    | SUniversal | SLpm _ -> s
    | SRange _ | SValueSet _ -> failwith "unreachable"

  and bits_of_lpmmask (acc : Bigint.t) (b : bool) (v : Bigint.t) : Bigint.t =
    let two = Bigint.(one + one) in
    if Bigint.(v = zero)
    then acc
    else if Bigint.(v % two = zero)
    then if b then failwith "bad lpm mask"
          else bits_of_lpmmask acc b Bigint.(v / two)
    else bits_of_lpmmask Bigint.(acc + one) true Bigint.(v/two)

  and eval_app' (ctrl : ctrl) (env : env) (st : state) (s : signal)
      (args : coq_Expression list) (t : coq_P4Type) : env * state * signal =
    let (st', sign', v) = eval_nameless env st t  [] in
    let typname = name_only (name_of_type_ref t) in
    let args' = List.map ~f:(fun arg -> Some arg) args in
    let env'' = Eval_env.set_namespace (Eval_env.get_namespace env ^ typname) env in
    let (st'', sign'', _) = eval_app ctrl env'' st' sign' v args' in
    (Eval_env.set_namespace (Eval_env.get_namespace env) env'', st'', sign'')

  and eval_cond (ctrl : ctrl) (env : env) (st : state) (sign : signal) (cond : coq_Expression)
      (tru : coq_Statement) (fls : coq_Statement option) : env * state * signal =
    let eval_cond' env cond tru fls =
      let (st', s', v) = eval_expr env st SContinue cond in
      match s' with
      | SReject _ -> (env, st', s')
      | SContinue ->
        begin match v with
          | VBool true  ->
            tru
            |> eval_stmt ctrl (Eval_env.push_scope env) st' SContinue
            |> Tuple.T3.map_fst ~f:(fun _ -> env)
          | VBool false ->
            begin match fls with
              | None -> (env, st', SContinue)
              | Some fls' ->
                fls'
                |> eval_stmt ctrl (Eval_env.push_scope env) st' SContinue
                |> Tuple.T3.map_fst ~f:(fun _ -> env)
            end
          | _ -> failwith "conditional guard must be a bool" end
      | _ -> failwith "unreachable" in
    match sign with
    | SContinue -> eval_cond' env cond tru fls
    | SReject _ | SReturn _ | SExit -> (env, st, sign)

  and eval_block (ctrl : ctrl) (env : env) (st : state) (sign :signal)
      (block : coq_Block) : (env * state * signal) =
    let block = snd block in
    let f (env,st,sign) stm =
      match sign with
      | SContinue -> eval_stmt ctrl env st sign stm
      | SReject _ | SReturn _ | SExit -> (env, st, sign) in
    block.statements
    |> List.fold_left ~init:(Eval_env.push_scope env,st,sign) ~f:f
    |> Tuple.T3.map_fst ~f:(fun _ -> env)

  and eval_exit (env : env) (st : state) (sign : signal) : (env * state * signal) =
    match sign with
    | SContinue -> (env, st, SExit)
    | SReturn v -> (env, st, SReturn v)
    | SExit -> (env, st, SExit)
    | SReject _ -> failwith "reject and exit in the same block"

  and eval_return (ctrl : ctrl) (env : env) (st : state) (sign : signal)
      (expr : coq_Expression option) : env * state * signal =
    let (st', s', v) =
      match expr with
      | None   -> (st, SContinue, VNull)
      | Some e -> eval_expr env st SContinue e in
    match sign with
    | SReject _ | SReturn _ | SExit -> (env,st,sign)
    | SContinue -> begin match s' with
      | SContinue -> (env, st', SReturn v)
      | SReject _ -> (env, st', s')
      | SReturn _ | SExit -> failwith "unreachable" end

  and eval_switch (ctrl : ctrl) (env : env) (st : state) (sign : signal) (expr : coq_Expression)
      (cases : Statement.switch_case list) : env * state * signal =
    let open Statement in
    let (st',s',v) = eval_expr env st SContinue expr in
    match sign with
    | SReject _ | SReturn _ | SExit -> (env, st, sign)
    | SContinue -> match s' with
      | SReject _ -> (env, st', s')
      | SContinue ->
        let s = assert_enum_field v |> snd in
        let matches = cases
          |> List.map ~f:snd
          |> List.group ~break:(fun x _ -> match x with Action _ -> true | _ -> false)
          |> List.filter ~f:(fun l -> List.exists l ~f:(label_matches_string s)) in
        begin match matches with
          | [] -> (env, st', s')
          | hd::tl -> hd
            |> List.filter ~f:(function Action _ -> true | _ -> false)
            |> List.hd_exn
            |> (function Action{label;code} -> code | _ -> failwith "unreachable")
            |> eval_block ctrl env st' SContinue
        end
      | _ -> failwith "unreachable"

  and eval_declaration_stm (ctrl : ctrl) (env : env) (st : state) (sign : signal)
      (decl : coq_Declaration) : env * state * signal =
    match sign with
    | SReject _ | SReturn _ | SExit -> (env, st, sign)
    | SContinue ->
      let (env, st) = eval_declaration ctrl env st decl in
      env, st, SContinue

  (*----------------------------------------------------------------------------*)
  (* Functions on L-Values*)
  (*----------------------------------------------------------------------------*)

  and lvalue_of_expr (env : env) (st : state) (signal : signal)
      (expr : coq_Expression) : state * signal * coq_ValueLvalue option =
    match signal with
    | SContinue -> begin match (snd expr).expr with
      | Name name -> st, SContinue, Some {lvalue = LName {name}; typ = (snd expr).typ}
      | ExpressionMember{expr=e; name=(_,n)} -> lvalue_of_expr_mem env st (snd expr).typ e n
      | BitStringAccess{bits;lo;hi} -> lvalue_of_expr_bsa env st (snd expr).typ bits lo hi
      | ArrayAccess{array=a;index} -> lvalue_of_expr_ara env st (snd expr).typ a index
      | _ -> st, signal, None end
    | SReject _ | SExit | SReturn _ -> st, signal, None

  and lvalue_of_expr_mem (env : env) (st : state) (typ : coq_P4Type)
      (e : coq_Expression) (n : string) : state * signal * coq_ValueLvalue option =
    let (st', signal, lv) = lvalue_of_expr env st SContinue e in
    st', signal,
    lv >>| fun lv -> {lvalue = LMember {expr = lv; name = n}; typ }

  and lvalue_of_expr_bsa (env : env) (st : state) (typ : coq_P4Type)
      (n : coq_Expression) (lsb : Bigint.t)
      (msb : Bigint.t) : state * signal * coq_ValueLvalue option =
    let (st', signal, lv) = lvalue_of_expr env st SContinue n in
    match signal with
    | SReject _ | SExit | SReturn _ -> st', signal, lv
    | SContinue ->
      st', signal,
      lv >>| fun lv -> {lvalue = LBitAccess{expr=lv; msb = msb; lsb = lsb}; typ}

  and lvalue_of_expr_ara (env : env) (st : state) (typ : coq_P4Type)
      (a : coq_Expression) (idx : coq_Expression) : state * signal * coq_ValueLvalue option =
    let (st', s, lv) = lvalue_of_expr env st SContinue a in
    let (st'', s', idx_val) = eval_expr env st' SContinue idx in
    let idx_bigint = bigint_of_val idx_val in
    match s, s' with
    | SContinue, SContinue ->
      st'', s',
      lv >>| fun lv -> {lvalue = LArrayAccess{expr=lv; idx=idx_bigint}; typ }
    | SContinue, _ -> st'', s', lv
    | _, _ -> st', s, lv

  (*----------------------------------------------------------------------------*)
  (* Expression Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_expr (env : env) (st : state) (s : signal)
      (exp : coq_Expression) : state * signal * coq_Value =
    match s with
    | SContinue ->
      let ctrl = (([],[]), []) in
      begin match (snd exp).expr with
        | True                              -> (st, s, VBool true)
        | False                             -> (st, s, VBool false)
        | Int(_,n)                          -> (st, s, eval_p4int n)
        | String (_,value)                  -> (st, s, VString value)
        | Name name                         -> eval_name env st name exp
        | ArrayAccess{array=a; index=i}     -> eval_array_access env st a i
        | BitStringAccess({bits;lo;hi})     -> eval_bitstring_access env st bits hi lo
        | Record{entries}                   -> eval_record env st entries
        | List{values}                      -> eval_list env st values
        | UnaryOp{op;arg}                   -> eval_unary env st op arg
        | BinaryOp{op; args=(l,r)}          -> eval_binop env st op l r
        | Cast{typ;expr}                    -> eval_cast env st typ expr
        | TypeMember{typ;name}              -> eval_typ_mem env st typ (snd name)
        | ErrorMember t                     -> (st, s, VError (snd t))
        | ExpressionMember{expr;name}       -> eval_expr_mem env st expr name
        | Ternary{cond;tru;fls}             -> eval_ternary env st cond tru fls
        | FunctionCall{func;args;type_args} -> eval_funcall ctrl env st func type_args args
        | NamelessInstantiation{typ;args}   -> eval_nameless env st typ args
        | Mask{expr;mask}                   -> eval_mask env st expr mask
        | Range{lo;hi}                      -> eval_range env st lo hi
        | DontCare                          -> st, s, VNull end
    | SReject _ -> (st, s, VNull)
    | SReturn _ -> failwith "expression should not return"
    | SExit -> failwith "expresion should not exit"

  and eval_name (env : env) (st : state) (name : Types.name)
      (exp : coq_Expression) : state * signal * coq_Value =
    let s = SContinue in
    (st, s, Eval_env.find_val name env |> extract_from_state st)

  and eval_p4int (n : P4Int.pre_t) : coq_Value =
    match n.width_signed with
    | None          -> VInteger n.value
    | Some(w,true)  -> VInt {w=Bigint.of_int w;v=n.value}
    | Some(w,false) -> VBit {w=Bigint.of_int w;v=n.value}

  and eval_array_access (env : env) (st : state) (a : coq_Expression)
      (i : coq_Expression) : state * signal * coq_Value =
    let (st', s, a') = eval_expr env st SContinue a in
    let (st'', s', i') = eval_expr env st' SContinue i in
    let idx = bigint_of_val i' in
    let (hdrs,size,next) = assert_stack a' in
    let idx' = Bigint.(to_int_exn (idx % size)) in
    let v = List.nth_exn hdrs idx' in
    match (s,s') with
    | SContinue, SContinue -> (st'', SContinue, v)
    | SReject _,_ -> (st',s, VNull)
    | _,SReject _ -> (st'',s',VNull)
    | _ -> failwith "unreachable"

  and eval_bitstring_access (env : env) (st : state) (b : coq_Expression)
      (m : Bigint.t) (l : Bigint.t) : state * signal * coq_Value =
    let (st', s, b) = eval_expr env st SContinue b in
    let b' = bigint_of_val b in
    let w = Bigint.(m-l + one) in
    let n = bitstring_slice b' m l in
    match s with
    | SContinue -> (st', SContinue, VBit{w;v=n})
    | SReject _ | SExit | SReturn _ -> (st',s,VNull)

  and eval_record (env : env) (st : state)
      (kvs : KeyValue.t list) : state * signal * coq_Value =
    let es = List.map kvs ~f:(fun kv -> (snd kv).value) in
    let ks = List.map kvs ~f:(fun kv -> snd (snd kv).key) in
    let f (b,c) d =
      let (x,y,z) = eval_expr env b c d in
      ((x,y),z) in
    es
    |> List.fold_map ~f:f ~init:(st, SContinue)
    |> (fun ((st,s),l) -> st,s, VRecord (List.zip_exn ks l))

  and eval_list (env : env) (st : state)
      (values : coq_Expression list) : state * signal * coq_Value =
    let f (b,c) d =
      let (x,y,z) = eval_expr env b c d in
      ((x,y),z) in
    values
    |> List.fold_map ~f:f ~init:(st,SContinue)
    |> (fun ((st,s),l) -> (st, s, VTuple l))

  and eval_unary (env : env) (st : state) (op : Op.uni)
      (e : coq_Expression) : state * signal * coq_Value =
    let (st', s, v) = eval_expr env st SContinue e in
    match s with
    | SContinue ->
       let v = Ops.interp_unary_op op v in
      (st', s,v)
    | SReject _ -> (st',s,VNull)
    | _ -> failwith "unreachable"

  and eval_binop (env : env) (st : state) (op : Op.bin) (l : coq_Expression)
      (r : coq_Expression) : state * signal * coq_Value =
    let shortcircuit env st l r f =
      let st, s, l = eval_expr env st SContinue l in
      match s with SReject _ | SReturn _ | SExit -> st, s, VNull
      | SContinue ->
        if l |> assert_bool |> f
        then st, s, l
        else eval_expr env st SContinue r in
    match snd op with
    | And -> shortcircuit env st l r not
    | Or -> shortcircuit env st l r ident
    | _ ->
      let (st',s,l) = eval_expr env st SContinue l in
      let (st'',s',r) = eval_expr env st' SContinue r in
      let v = Ops.interp_binary_op op l r in
      begin match (s,s') with
        | SContinue, SContinue -> (st'', SContinue, v)
        | SReject _,_ -> (st',s,VNull)
        | _,SReject _ -> (st'',s',VNull)
        | _ -> failwith "unreachable"
      end

  and eval_cast (env : env) (st : state) (typ : coq_P4Type)
      (expr : coq_Expression) : state * signal * coq_Value =
    let (st', s, v) = eval_expr env st SContinue expr in
    let v' = Ops.interp_cast typ v
      ~type_lookup:(fun name -> Eval_env.find_typ name env) in
    match s with
    | SContinue -> (st',s,v')
    | _ -> (st',s,VNull)

  and eval_typ_mem (env : env) (st : state) (typ : Types.name)
      (enum_name : string) : state * signal * coq_Value =
    match Eval_env.find_typ typ env with
    | Enum {name; typ = None; members} ->
      if List.mem members enum_name ~equal:String.equal
      then (st, SContinue, VEnumField{typ_name=name;enum_name})
      else raise (UnboundName name)
    | Enum {name; typ = Some _; members} ->
      begin match Eval_env.find_val typ env |> extract_from_state st with
        | VSenum fs ->
          let v = find_exn fs enum_name in
          st, SContinue, VSenumField{typ_name=name;enum_name;v}
        | _ -> failwith "typ mem undefined"
      end
    | _ -> failwith "type mem undefined"

  and eval_expr_mem (env : env) (st : state) (expr : coq_Expression)
      (name : P4String.t) : state * signal * coq_Value =
    let (st', s, v) = eval_expr env st SContinue expr in
    let third3 (_,_,x) = x in
    match s with
    | SContinue ->
      begin match v with
        | VStruct{fields=fs} ->
          eval_struct_mem env st' (snd name) fs
        | VHeader{fields=fs;is_valid=vbit} ->
          eval_header_mem env st' (snd name) expr fs vbit
        | VUnion{fields=fs} ->
          eval_union_mem env st' (snd name) expr fs
        | VStack{headers=hdrs;size=s;next=n} ->
          eval_stack_mem env st' (snd name) expr hdrs s n
        | VRuntime {loc; obj_name} ->
          eval_runtime_mem env st' (snd name) expr loc obj_name
        | VRecord fs ->
          st', s, find_exn fs (snd name)
        | VParser _ | VControl _ | VTable _ ->
          let name = snd name in
          let caller = lvalue_of_expr env st' SContinue expr
            |> third3
            |> Option.value_exn in
          st', s, VBuiltinFun { name; caller; }
        | _ -> failwith "type member does not exists"
      end
    | SReject _ -> (st',s,VNull)
    | _ -> failwith "unreachable"

  and eval_ternary (env : env) (st : state) (c : coq_Expression)
      (te : coq_Expression) (fe : coq_Expression) : state * signal * coq_Value =
    let (st', s, c') = eval_expr env st SContinue c in
    match c' with
    | VBool(true)  -> (eval_expr env st' s te)
    | VBool(false) -> (eval_expr env st' s fe)
    | _ -> failwith "ternary guard must be a bool"

  and eval_funcall (ctrl : ctrl) (env : env) (st : state) (func : coq_Expression)
      (targs : coq_P4Type list)
      (args : coq_Expression option list) : state * signal * coq_Value =
    let (st', s, cl) = eval_expr env st SContinue func in
    match s with
    | SContinue -> begin match cl with
      | VAction{scope;params; body} | VFun{scope;params; body} ->
        eval_funcall' env st' scope params args body
      | VBuiltinFun{name=n;caller=lv} ->
        eval_builtin ctrl env st' n lv args
      | VExternFun{name=n;caller=v;params} ->
        eval_extern_call env st' n v params targs args
      | _ -> failwith "unreachable" end
    | SReject _ -> (st',s,VNull)
    | _ -> failwith "unreachable"

  and eval_nameless (env : env) (st : state) (typ : coq_P4Type)
      (args : coq_Expression list) : state * signal * coq_Value =
    let name = name_of_type_ref typ in
    let args' = List.map ~f:(fun arg -> Some arg) args in
    match Eval_env.find_val name env |> extract_from_state st with
    | VPackage {params;_} ->
      let (_, env,st,s) = (env --> env) st params args' in
      let args = env |> Eval_env.get_val_firstlevel |> List.rev in
      (st, s, VPackage{params;args;})
    | VControl {cscope;cconstructor_params;cparams;clocals;apply} ->
      let (_, cscope,st,s) = (env --> cscope) st cconstructor_params args' in
      let v = VControl { cscope; cconstructor_params; cparams; clocals; apply; } in
      (st,s,v)
    | VParser {pscope;pconstructor_params;pparams;plocals;states} ->
      let (_, pscope,st,s) = (env --> pscope) st pconstructor_params args' in
      let v = VParser {pscope; pconstructor_params; pparams; plocals; states; } in
      (st,s,v)
    | VExternObj ps ->
      let loc = Eval_env.get_namespace env in
      if State.is_initialized loc st
      then st, SContinue, VRuntime {loc = loc; obj_name = name_only name; }
      else 
        let params = List.Assoc.find_exn ps (name_only name) ~equal:String.equal in
        eval_extern_call env st (name_only name) (Some (loc, name_only name)) params [] args'
    | _ -> failwith "instantiation unimplemented"

  and eval_mask (env : env) (st : state) (e : coq_Expression)
      (m : coq_Expression) : state * signal * coq_Value =
    let (st', s, v1)  = eval_expr env st SContinue e in
    let (st'', s', v2) = eval_expr env st' SContinue m in
    match (s,s') with
    | SContinue, SContinue ->
      (st'', s, VSet(SMask{v=v1;mask=v2}))
    | SReject _,_ -> (st',s,VNull)
    | _,SReject _ -> (st'',s',VNull)
    | _ -> failwith "unreachable"

  and eval_range (env : env) (st : state) (lo : coq_Expression)
      (hi : coq_Expression) : state * signal * coq_Value =
    let (st', s, v1) = eval_expr env st SContinue lo in
    let (st'',s',v2) = eval_expr env st' SContinue hi in
    match (s,s') with
    | SContinue, SContinue -> (st'', s, VSet(SRange{lo=v1;hi=v2}))
    | SReject _,_ -> (st',s,VNull)
    | _,SReject _ -> (st'',s',VNull)
    | _ -> failwith "unreachable"

  (*----------------------------------------------------------------------------*)
  (* Membership Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_struct_mem (env : env) (st : state) (name : string)
      (fs : (string * coq_Value) list) : state * signal * coq_Value =
    (st, SContinue, (find_exn fs name))

  and eval_header_mem (env : env) (st : state) (fname : string)
      (e : coq_Expression) (fs : (string * coq_Value) list)
      (valid : bool) : state * signal * coq_Value =
    match fname with
    | "setValid" | "setInvalid" ->
      let (_, _, lv) = lvalue_of_expr env st SContinue e in
      st, SContinue, VBuiltinFun{name=fname;caller=Option.value_exn lv}
    | "isValid" -> begin try
      let (_, _, lv) = lvalue_of_expr env st SContinue e in
      st, SContinue, VBuiltinFun{name=fname; caller=Option.value_exn lv}
      with _ -> failwith "TODO: edge case with header isValid()" end
    | _ -> (st, SContinue, T.read_header_field valid fs fname)

  and eval_union_mem (env : env) (st : state)
    (fname : string) (e : coq_Expression) (fs : (string * coq_Value) list)
    : state * signal * coq_Value =
    let (st', signal, lv) = lvalue_of_expr env st SContinue e in
    match fname with
    | "isValid" -> begin match signal, lv with
      | SContinue, Some lv -> st', SContinue, VBuiltinFun{name=fname;caller=lv}
      | _, _ -> st', signal, VNull end
    | _ -> (st, SContinue, (find_exn fs fname))

  and eval_stack_mem (env : env) (st : state) (fname : string)
      (e : coq_Expression) (hdrs : coq_Value list) (size : Bigint.t)
      (next : Bigint.t) : state * signal * coq_Value =
    match fname with
    | "size" -> eval_stack_size env st size
    | "next" -> eval_stack_next env st hdrs size next
    | "last" -> eval_stack_last env st hdrs size next
    | "lastIndex" -> eval_stack_lastindex env st next
    | "pop_front" | "push_front" ->
      eval_stack_builtin env st fname e
    | _ -> failwith "stack member unimplemented"

  and eval_runtime_mem (env : env) (st : state) (mname : string) (expr : coq_Expression)
      (loc : loc) (obj_name : string) : state * signal * coq_Value =
    let params = Eval_env.find_val (BareName (Info.dummy, obj_name)) env
      |> (fun l -> State.find_heap l st)
      |> assert_externobj
      |> fun l -> List.Assoc.find_exn l mname ~equal:String.equal in
    st, SContinue, VExternFun {caller = Some (loc, obj_name); name = mname; params }

  and eval_stack_size (env : env) (st : state)
      (size : Bigint.t) : state * signal * coq_Value =
    let five = Bigint.(one + one + one + one + one) in
    let thirty_two = shift_bitstring_left Bigint.one five in
    (st, SContinue, VBit{w=thirty_two;v=size})

  and eval_stack_next (env : env) (st : state) (hdrs : coq_Value list) (size : Bigint.t)
      (next : Bigint.t) : state * signal * coq_Value =
    if Bigint.(next >= size)
    then st, SReject "StackOutOfBounds", VNull
    else st, SContinue, List.nth_exn hdrs Bigint.(to_int_exn next)

  and eval_stack_last (env : env) (st : state) (hdrs : coq_Value list) (size : Bigint.t)
      (next : Bigint.t) : state * signal * coq_Value =
    if Bigint.(next < one) || Bigint.(next > size)
    then st, SReject "StackOutOfBounds", VNull
    else st, SContinue, List.nth_exn hdrs Bigint.(to_int_exn (next - one))

  and eval_stack_lastindex (env : env) (st : state)
      (next : Bigint.t) : state * signal * coq_Value =
    st, SContinue, Bigint.(VBit {w= of_int 32; v= next - one})

  and eval_stack_builtin (env : env) (st : state) (name : string)
      (e : coq_Expression) : state * signal * coq_Value =
    let (st', signal, lv) = lvalue_of_expr env st SContinue e in
    st', signal, VBuiltinFun{name; caller = Option.value_exn lv}

  (*----------------------------------------------------------------------------*)
  (* Function and Method Call Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_extern_call (callenv : env) (st : state) (name : string)
      (v : (loc * string) option) (params : coq_P4Parameter list) (targs : coq_P4Type list)
      (args : coq_Expression option list) : state * signal * coq_Value =
    let ts = args |> List.map ~f:(function Some e -> (snd e).typ | None -> Void) in
    let params =
      match v with
      | Some (_,t) ->
        Eval_env.find_val (BareName (Info.dummy, t)) callenv
        |> extract_from_state st
        |> assert_externobj
        |> List.filter ~f:(fun (s,_) -> String.equal s name)
        |> List.filter ~f:(fun (_,ps) -> Int.equal (List.length ps) (List.length args))
        |> List.hd_exn
        |> snd
      | None ->
        Eval_env.find_val (BareName (Info.dummy, name)) callenv
        |> extract_from_state st
        |> assert_externfun in
    let (_,kvs) =
      List.fold_mapi args ~f:(eval_nth_arg callenv st params) ~init:([], st,SContinue) in
    let (lvs, fenv, st', signal) = (callenv --> callenv) st params args in
    let vs = List.map ~f:snd kvs in
    match signal with
    | SExit -> st', SExit, VNull
    | SReject s -> st', SReject s, VNull
    | SReturn _ | SContinue ->
    let tvs = List.zip_exn vs ts in
    let tvs' = match v with
      | Some (loc, t) -> (VRuntime {loc = loc; obj_name = t;},
                          Type.TypeName (BareName (Info.dummy, "packet"))) :: tvs
      | None -> tvs in
    let (fenv', st'', s, v) = T.eval_extern name fenv st' targs tvs' in
    let st'' = (callenv <-- fenv') st'' params lvs in
    st'', s, v

  and eval_funcall' (callenv : env) (st : state) (fscope : env)
      (params : coq_P4Parameter list) (args : coq_Expression option list)
      (body : coq_Block) : state * signal * coq_Value =
    let (lvs, fenv, st', s) = (callenv --> fscope) st params args in
    let (fenv', st'', sign) = eval_block (([],[]),[]) fenv st' SContinue body in
    let st'' = (callenv <-- fenv') st'' params lvs in
    match sign with
    | SReturn v -> (st'', SContinue, v)
    | SReject _
    | SContinue
    | SExit     -> (st'', sign, VNull)

  (** [copyin callenv clenv st params args] returns the following three values:
      1 the env [clenv'] which is the closure environment with a fresh scope
         pushed on and the args inserted under the parameter names
      2) a new state in which to evaluate the body, resulting from evaluating
         the args under the [callenv].
      3) a signal indicating the success or failure of evaluating the args. 
      
      For readability, we introduce the notation [callenv --> clenv] to mean
      [copyin callenv clenv]. *)
  and (-->) (callenv : env) (fscope : env) : state -> coq_P4Parameter list ->
      coq_Expression option list -> coq_ValueLvalue option list * env * state * signal = fun st params args ->
    let fenv = Eval_env.push_scope fscope in
    let f = eval_nth_arg callenv st params in
    let (lvs, st, s), arg_vals = List.fold_mapi args ~f ~init:([],st,SContinue) in
    let fenv, st = List.fold2_exn params arg_vals ~init:(fenv, st) ~f:insert_arg in
    List.rev lvs, fenv, st, s

  (** [copyout callenv clenv st params args] returns the updated state
      [st'] which is [st] with the out args copied from the clenv into the
      callenv. [calllenv] should be the original [callenv] used by [copyin], and
      [clenv] should be the environment resulting from copying in and evaluating
      the function body.
      
      For readability, we introduce the notation [callenv <-- clenv] to mean
      [copyout callenv clenv]. *)
  and (<--) (callenv:env) (fenv : env) : state -> coq_P4Parameter list ->
      coq_ValueLvalue option list -> state = fun st ->
    List.fold2_exn ~init:st ~f:(copy_arg_out fenv callenv)

  and eval_nth_arg (env : env) (st : state) (params : coq_P4Parameter list) (i : int)
      (lvs, st, sign : coq_ValueLvalue option list * state * signal)
      (e : coq_Expression option) : (coq_ValueLvalue option list * state * signal) * (string * coq_Value) =
    let p = List.nth_exn params i in
    let ((st',s,lv), n) = match e with
      | Some expr -> lvalue_of_expr env st SContinue expr, snd p.variable
      | None -> (st, SContinue, None), snd p.variable in
    let (st', s, v) = match lv with
      | Some lv -> st', s, value_of_lvalue env st' lv |> snd
      | None -> begin match e with
        | Some expr -> eval_expr env st SContinue expr
        | None -> (st, SContinue, VNull) end in
    match (sign,s) with
    | SContinue, SContinue -> (lv :: lvs, st', s), (n, v)
    | SReject _, _ -> (lv :: lvs, st, sign), (n, VNull)
    | _, SReject _ -> (lv :: lvs, st', s), (n, VNull)
    | _ -> failwith "unreachable"

  and insert_arg (e, st : Eval_env.t * state) (p : coq_P4Parameter)
      (name, v : string * coq_Value) : env * state =
    (* TODO: zero out v if dir = out *)
    let var = Types.BareName p.variable in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    Eval_env.insert_val var l e, st

  and copy_arg_out (fenv : env) (callenv : env) (st : state) (p : coq_P4Parameter)
      (a : coq_ValueLvalue option) : state =
    match p.direction with
    | InOut | Out -> copy_arg_out_h fenv st callenv p a
    | In | Directionless -> st

  and copy_arg_out_h (fenv : env) (st : state)
      (callenv : env) (p : coq_P4Parameter) (lv : coq_ValueLvalue option) : state =
    let v = Eval_env.find_val (BareName p.variable) fenv |> extract_from_state st in
    match lv with
    | None -> st
    | Some lv -> assign_lvalue st callenv lv v |> fst

  (*----------------------------------------------------------------------------*)
  (* Built-in Function Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_builtin (ctrl :ctrl) (env : env) (st : state) (name : string) (lv : coq_ValueLvalue)
      (args : coq_Expression option list) : state * signal * coq_Value =
    match name with
    | "isValid"    -> eval_isvalid env st lv
    | "setValid"   -> eval_setbool env st lv true
    | "setInvalid" -> eval_setbool env st lv false
    | "pop_front"  -> eval_push_pop env st lv args false
    | "push_front" -> eval_push_pop env st lv args true
    | "apply" ->
      let lvname = match lv.lvalue with
        | LName {name} -> name
        | _ -> failwith "bad apply" in
      let (s,v) = value_of_lvalue env st lv in
      eval_app ctrl (Eval_env.set_namespace (name_only lvname) env) st s v args
    | _ -> failwith "builtin unimplemented"

  and eval_isvalid (env : env) (st : state)
      (lv : coq_ValueLvalue) : state * signal * coq_Value =
    let (s,v) = value_of_lvalue env st lv in
    match s, v with
    | (SReturn _ | SExit | SReject _), _ -> (st, s, VNull)
    | SContinue, VHeader{is_valid=b;_} ->
      (st, s, VBool b)
    | SContinue, VUnion{fields} ->
      let field_valid (_, l) = snd (assert_header l) in
      let valid = List.exists ~f:field_valid fields in
      (st, s, VBool valid)
    | SContinue, _ ->
      failwith "isvalid call is not a header"

  and eval_setbool (env : env) (st : state) (lv : coq_ValueLvalue)
      (b : bool) : state * signal * coq_Value =
    let (s,v) = value_of_lvalue env st lv in
    match s, v with
    | (SReturn _ | SExit | SReject _), _ -> (st, s, VNull)
    | SContinue, VHeader hdr ->
       let st, signal = assign_lvalue st env lv (VHeader {hdr with is_valid = b}) in
       (st, signal, VBool b)
    | SContinue, _ ->
       failwith "isvalid call is not a header"

  and eval_push_pop (env : env) (st : state) (lv : coq_ValueLvalue)
      (args : coq_Expression option list) (b : bool) : state * signal * coq_Value =
    let (st', s, a) = eval_push_pop_args env st args in
    let (s',v) = value_of_lvalue env st lv in
    let (hdrs, size, next) =
      match v with
      | VStack{headers=hdrs;size;next} -> (hdrs,size,next)
      | _ -> failwith "push call not a header stack" in
    let x = if b then Bigint.(size - a) else a in
    let (hdrs1, hdrs2) = List.split_n hdrs Bigint.(to_int_exn x) in
    let t = match lv.typ with
      | Array{typ;_} -> typ
      | _ -> failwith "not a header stack" in
    let hdrs0 = List.init (Bigint.to_int_exn a) ~f:(fun x -> x) in
    let hdrs0 =
      List.map hdrs0 ~f:(fun _ -> init_val_of_typ env t) in
    let hdrs' = if b then hdrs0 @ hdrs1 else hdrs2 @ hdrs0 in
    let y = if b then Bigint.(next + a) else Bigint.(next-a) in
    let v = VStack{headers=hdrs';size;next=y} in
    match s,s' with
    | SContinue, SContinue ->
      let (st', _) = assign_lvalue st' env lv v in (st', s, VNull)
    | SReject _, _ -> (st',s,VNull)
    | _, SReject _ -> (st',s',VNull)
    | _ -> failwith "unreachble"

  and eval_push_pop_args (env : env) (st : state)
      (args : coq_Expression option list) : state * signal * Bigint.t =
    match args with
    | [Some value] ->
      let (st', s, v) = eval_expr env st SContinue value in
      begin match s with
        | SContinue -> (st', s, bigint_of_val v)
        | SReject _ -> (st', s, Bigint.zero)
        | _ -> failwith "unreachable" end
    | _ -> failwith "invalid push or pop args"

  (*----------------------------------------------------------------------------*)
  (* Parser Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_parser (ctrl : ctrl) (env : env) (st : state) (params : coq_P4Parameter list)
      (args : coq_Expression option list) (pscope : env)
      (locals : coq_Declaration list) (states : coq_ParserState list) : state * signal =
    let (lvs, penv, st, s) = (env --> pscope) st params args in
    match s with
    | SContinue ->
      let (penv, st) = List.fold_left locals ~init:(penv,st) ~f:(fun (e,s) -> eval_declaration ctrl e s) in
      let states' = List.map states ~f:(fun s -> snd (snd s).name, s) in
      let start = find_exn states' "start" in
      let (penv, st, final_state) = eval_state_machine ctrl penv st states' start in
      let st = (env <-- penv) st params lvs in
      (st, final_state)
    | SReject _ -> (st, s)
    | _ -> failwith "unreachable"

  and eval_state_machine (ctrl : ctrl) (env : env) (st : state)
      (states : (string * coq_ParserState) list)
      (state : coq_ParserState) : env * state * signal =
    let (stms, transition) =
      match snd state with
      | {statements=stms; transition=t;_} -> (stms, t) in
    let f (env, st, sign) stm =
      match sign with
      | SContinue -> eval_stmt ctrl env st sign stm
      | _ -> (env, st, sign) in
    let (env', st', sign) = List.fold ~f ~init:(Eval_env.push_scope env,st, SContinue) stms in
    match sign with
    | SContinue ->
      eval_transition ctrl env' st' states transition
      |> Tuple.T3.map_fst ~f:Eval_env.pop_scope
    | SReject _ -> (env', st', sign)
    | SReturn _ -> failwith "return statements not permitted in parsers"
    | SExit -> failwith "exit statements not permitted in parsers"

  and eval_transition (ctrl : ctrl) (env : env) (st : state)
      (states : (string * coq_ParserState) list)
      (transition : Parser.transition) : env * state * signal =
    match snd transition with
    | Direct{next = (_, next)} -> eval_direct ctrl env st states next
    | Select{exprs;cases} -> eval_select ctrl env st states exprs cases

  and eval_direct (ctrl : ctrl) (env : env) (st : state)
      (states : (string * coq_ParserState) list) (next : string) : env * state * signal =
    match next with
    | "accept" -> env, st, SContinue
    | "reject" -> env, st, SReject "NoError"
    | _        -> eval_state_machine ctrl env st states (find_exn states next)

  and eval_select (ctrl : ctrl) (env : env) (st : state)
      (states : (string * coq_ParserState) list) (exprs : coq_Expression list)
      (cases : Parser.case list) : env * state * signal =
    let f (st,s) e =
      let (b,c,d) = eval_expr env st s e in
      ((b,c),d) in
    let ((st', s), vs) = List.fold_map exprs ~init:(st,SContinue) ~f:f in
    let ws = List.map vs ~f:(width_of_val) in
    match s with
    | SContinue ->
      let g (e,st,s) coq_ValueSet =
        let (w,x,y,z) = set_of_case ctrl e st s set ws in
        ((w,x,y),(z,w,x)) in
      let ((env'',st'', s), ss) = List.fold_map cases ~init:(env, st', SContinue) ~f:g in
      let coerce_value_set s =
        match s with
        | SValueSet {size=si;members=ms;_},e,st ->
          let h (a,b,c) d =
            let (w,x,y,z) = set_of_matches ctrl a b c d ws in
            ((w,x,y),z) in
          let ((e',st',_),ss) = List.fold_map ms ~init:(e,st,SContinue) ~f:h in
          (SValueSet {size=si;members=ms;sets=ss},e',st')
        | x -> x in
      let ss' = List.map ss ~f:coerce_value_set in
      let ms = List.map ss' ~f:(fun (x,y,z) -> (values_match_set st'' vs x, y,z)) in
      let ms' = List.zip_exn ms cases
                |> List.map ~f:(fun ((b,env,st),c) -> (b,(env,st,c))) in
      let next = List.Assoc.find ms' true ~equal:Poly.(=) in
      begin match next with
        | None -> (env'', st'', SReject "NoMatch")
        | Some (fenv,st,next) ->
          let next' = snd (snd next).next in
          eval_direct ctrl fenv st states next' end
    | SReject _ -> (env,st', s)
    | _ -> failwith "unreachable"

  (* -------------------------------------------------------------------------- *)
  (* Control Evaluation *)
  (* -------------------------------------------------------------------------- *)

  and eval_control (ctrl : ctrl) (env : env) (st : state) (params : coq_P4Parameter list)
      (args : coq_Expression option list) (cscope : env)
      (locals : coq_Declaration list) (apply : coq_Block) : state * signal =
    let (lvs, cenv,st,_) = (env --> cscope) st params args in
    let (cenv,st) = List.fold_left locals ~init:(cenv,st) ~f:(fun (e,st) s -> eval_declaration ctrl e st s) in
    let block =
      (Info.dummy,
      {stmt = Statement.BlockStatement {block = apply};
      typ = Unit}) in
    let (cenv, st, sign) = eval_stmt ctrl cenv st SContinue block in
    (env <-- cenv) st params lvs, sign

  (*----------------------------------------------------------------------------*)
  (* Set Evaluation *)
  (*----------------------------------------------------------------------------*)  

  and set_of_case (ctrl : ctrl) (env : env) (st : state) (s : signal)
      (case : Parser.case) (ws : Bigint.t list) : env * state * signal * coq_ValueSet =
    match s with
    | SContinue -> set_of_matches ctrl env st s (snd case).matches ws
    | SReject _ -> (env,st,s,SUniversal)
    | _ -> failwith "unreachable"

  and set_of_matches (ctrl : ctrl) (env : env) (st : state) (s : signal)
      (ms : Match.t list) (ws : Bigint.t list) : env * state * signal * coq_ValueSet =
    match ms,ws with
    | [],_ -> failwith "invalid set"
    | [m],[w] -> set_of_match ctrl env st s m w
    | l,ws ->
      let f i (a,b,c) d =
        let (w,x,y,z) = set_of_match ctrl a b c d (List.nth_exn ws i) in
        ((w,x,y),z) in
      let ((env',st',s),l') = List.fold_mapi l ~init:(env,st,SContinue) ~f:f in
      (env',st',s,SProd l')

  and set_of_match (ctrl : ctrl) (env : env) (st : state) (s : signal)
      (m : Match.t) (w : Bigint.t) : env * state * signal * coq_ValueSet =
    match s with
    | SContinue ->
      begin match (snd m).expr with
        | DontCare         -> (env, st, SContinue, SUniversal)
        | Expression{expr} ->
          let (st', s, v) = eval_expr env st SContinue expr in
          (env, st', s, assert_set v w) end
    | SReject _ -> (env, st, s, SUniversal)
    | _ -> failwith "unreachable"

  and values_match_set (st : state) (vs : coq_Value list) (s : coq_ValueSet) : bool =
    match s with
    | SSingleton{w;v}     -> values_match_singleton vs v
    | SUniversal          -> true
    | SMask{v=v1;mask=v2} -> values_match_mask st vs v1 v2
    | SRange{lo=v1;hi=v2} -> values_match_range vs v1 v2
    | SProd l             -> values_match_prod st vs l
    | SLpm{w=v1;v=v2;_}   -> values_match_mask st vs v1 v2
    | SValueSet {sets=ss;_}   -> values_match_value_set st vs ss

  and values_match_singleton (vs : coq_Value list) (n : Bigint.t) : bool =
    let v = List.hd_exn vs in
    v |> bigint_of_val |> (Bigint.(=) n)

  and values_match_mask (st : state) (vs : coq_Value list) (v1 : coq_Value)
      (v2 : coq_Value) : bool =
    let two = Bigint.(one + one) in
    let v = List.hd_exn vs in
    let (a,b,c) = assert_bit v, assert_bit v1, assert_bit v2 in
    let rec h (w0,b0) (w1,b1) (w2,b2) =
      if not (Bigint.(w0 = w1) && Bigint.(w1 = w2))
      then false
      else if Bigint.(w0 = zero)
      then true
      else if Bigint.(b2%two = zero) || Bigint.(b1%two = b0%two)
      then h Bigint.(w0-one, b0/two) Bigint.(w1-one, b1/two) Bigint.(w2-one, b2/two)
      else false in
    h a b c

  and values_match_range (vs : coq_Value list) (low_bound : coq_Value) (high_bound : coq_Value) : bool =
    let v = bigint_of_val (List.hd_exn vs) in
    let low_bound = bigint_of_val low_bound in
    let high_bound = bigint_of_val high_bound in
    Bigint.(low_bound <= v && v <= high_bound)

  and values_match_prod (st : state) (vs : coq_Value list) (l : coq_ValueSet list) : bool =
    let bs = List.mapi l ~f:(fun i x -> values_match_set st [List.nth_exn vs i] x) in
    List.for_all bs ~f:(fun b -> b)

  and values_match_value_set (st : state) (vs : coq_Value list) (l : coq_ValueSet list) : bool =
    let bs = List.map l ~f:(values_match_set st vs) in
    List.exists bs ~f:(fun b -> b)

  (*----------------------------------------------------------------------------*)
  (* Helper functions *)
  (*----------------------------------------------------------------------------*)

  and extract_from_state (st : state) (l : loc) : coq_Value =
    State.find_heap l st

  and name_only (name: Typed.name) =
    match name with
    | BareName s
    | QualifiedName (_, s) -> s

  and label_matches_string (s : string) (case : coq_StatementSwitchCase) : bool =
    match case with
    | StatSwCaseAction (_, label, _)
    | StatSwCaseFallThrough (_, label) ->
      match label with
      | StatSwLabDefault _ -> true
      | StatSwLabName (_, (MkP4String (_, name))) ->
        String.equal s name

  and name_of_type_ref (typ: coq_P4Type) : Typed.name =
    match typ with
    | TypTypeName name -> name
    | TypNewType (name, _) -> BareName name
    | TypEnum (name, _, _) -> BareName name
    | TypSpecializedType (base, _) ->
        name_of_type_ref base
    | _ -> failwith "can't find name for this type"

  and eval_statement ctrl env st s =
    let (a,b,_) = eval_stmt ctrl env st SContinue s in (a,b)

  and eval_expression env st expr =
    let (b,_,c) = eval_expr env st SContinue expr in (b,c)

  and eval (ctrl : ctrl) (env : env) (st : state) (pkt : pkt)
      (in_port : Bigint.t) : state * env * pkt option * Bigint.t =
    let st' = T.initialize_metadata in_port st in
    let (st, env, pkt) = T.eval_pipeline ctrl env st' pkt eval_app in
    st, env, pkt, T.get_outport st env

  and eval_main (ctrl : ctrl) (env : env) (st : state) (pkt : pkt)
      (in_port : Bigint.t) : state * pkt option * Bigint.t =
    let (st, _, pkt, out_port) = eval ctrl env st pkt in_port in
    st, pkt, out_port

  and eval_program (ctrl : ctrl) (env: env) (st : state) (pkt : buf)
      (in_port : Bigint.t) (prog : program) : state * (buf * Bigint.t) option =
    let (>>|) = Option.(>>|) in
    let st = State.reset_state st in
    let (env,st) =
      List.fold_left prog
        ~init:(env, st)
        ~f:(fun (e,s) -> eval_declaration ctrl e s)
    in
    let pkt = {emitted = Cstruct.empty; main = pkt; in_size = Cstruct.len pkt} in
    let st', pkt', port = eval_main ctrl env st pkt in_port in
    st', pkt' >>| fun pkt' -> (Cstruct.append pkt'.emitted pkt'.main, port)

end

(*----------------------------------------------------------------------------*)
(* Program Evaluation *)
(*----------------------------------------------------------------------------*)

module V1Interpreter = MakeInterpreter(V1model.V1Switch)

module EbpfInterpreter = MakeInterpreter(Ebpf.EbpfFilter)

module Up4Interpreter = MakeInterpreter(Up4.Up4Filter)
