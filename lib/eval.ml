module I = Info
open Core_kernel
open Prog
open Env
open Typed
open Value
open Target
open Bitstring
open Util
module Info = I (* JNF: ugly hack *)

let (>>|) v f = Option.map ~f:f v

type env = EvalEnv.t

module type Interpreter = sig

  type state

  val empty_state : state

  val eval_expression : ctrl -> env -> state -> Expression.t -> (state * value)

  val eval_statement : ctrl -> env -> state -> Statement.t -> (env * state)

  val eval_declaration : ctrl -> env -> state -> Declaration.t -> (env * state)

  val eval_program : ctrl -> env -> state -> buf -> Bigint.t -> Bigint.t -> program ->
    state * (buf * Bigint.t) list

  val init_switch : env -> program -> env * state

  val switch_packet : ctrl -> env -> state ->  buf -> Bigint.t -> Bigint.t ->
    state * (buf * Bigint.t) list

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
      (d : Declaration.t) : env * state =
    let open Declaration in
    match snd d with
    | Constant {typ; value; name; _ } ->
      eval_const_decl ctrl env st typ value (snd name)
    | Instantiation { typ; args; name; init = None; _ } -> 
      eval_instantiation ctrl env st typ args (snd name)
    | Instantiation { init = Some _; _ } ->
      failwith "abstract externs unsupported"
    | Parser { name; params; constructor_params; locals; states; _ } ->
      eval_parser_decl env st (snd name) constructor_params params locals states
    | Control { name; params; constructor_params; locals; apply; _ } ->
      eval_control_decl env st (snd name) constructor_params params locals apply
    | Function { name; params; body; _ } ->
      eval_fun_decl env st (snd name) params body
    | ExternFunction { name; params; _ } ->
      eval_extern_fun env st (snd name) params
    | Variable { typ; name; init; _ } ->
      let (a,b,_) = eval_var_decl ctrl env st typ (snd name) init in (a,b)
    | ValueSet { typ; size; name; _ } ->
      let (a,b,_) = eval_set_decl ctrl env st typ (snd name) size in (a,b)
    | Action { name; data_params; ctrl_params; body; _ } ->
      eval_action_decl env st (snd name) data_params ctrl_params body
    | Table { name; key; actions; entries; default_action; size; custom_properties; _ } ->
      eval_table_decl ctrl env st (snd name) key actions entries default_action size custom_properties
    | SerializableEnum { name; members; _ } ->
      eval_senum_decl ctrl env st (snd name) members
    | ExternObject { name; type_params; methods; _ } ->
      eval_extern_obj env st (snd name) methods
    | PackageType {name = (_,n); params; _ } ->
      eval_pkgtyp_decl env st n params
    | _ -> env, st

  and eval_const_decl (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (v : value) (name : string) : env * state =
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    EvalEnv.insert_val_bare name l env, st

  and eval_instantiation (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (args : Expression.t list) (name : string) : env * state =
    let env' = EvalEnv.set_namespace (EvalEnv.get_namespace env ^ name) env in
    let (st',_,obj) = eval_nameless ctrl env' st typ args in
    let env' = EvalEnv.set_namespace (EvalEnv.get_namespace env) env in
    let l = State.fresh_loc () in
    let st' = State.insert_heap l obj st' in
    (EvalEnv.insert_val_bare name l env', st')

  and eval_parser_decl (env : env) (st : state) (name : string)
      (constructor_params : Parameter.t list) (params : Parameter.t list)
      (locals : Declaration.t list) (states : Parser.state list) : env * state =
    let v = VParser {
      pscope = env;
      pconstructor_params = constructor_params;
      pparams = params;
      plocals = locals;
      states;
    } in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in 
    let env = EvalEnv.insert_val_bare name l env in
    env, st

  and eval_control_decl (env : env) (st : state) (name : string)
      (constructor_params : Parameter.t list) (params : Parameter.t list)
      (locals : Declaration.t list) (apply : Block.t) : env * state =
    let v = VControl {
      cscope = env;
      cconstructor_params = constructor_params;
      cparams = params;
      clocals = locals;
      apply = apply;
    } in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    let env = EvalEnv.insert_val_bare name l env in
    env, st

  and eval_fun_decl (env : env) (st : state) (name : string)
      (params : Parameter.t list) (body : Block.t) : env * state =
    let l = State.fresh_loc () in
    let st = State.insert_heap l (VFun{scope=env;params;body}) st in
    EvalEnv.insert_val_bare name l env, st

  and eval_extern_fun (env : env) (st : state) (name : string)
      (params : Parameter.t list) : env * state =
    let l = State.fresh_loc () in
    let st = State.insert_heap l (VExternFun {name; caller = None; params;}) st in
    EvalEnv.insert_val_bare name l env, st

  and eval_var_decl (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (name : string) (init : Expression.t option) : env * state * signal =
    let init_val = init_val_of_typ env typ in
    let l = State.fresh_loc () in
    let st = State.insert_heap l init_val st in
    match init with
    | None ->
      let env = EvalEnv.insert_val_bare name l env in
      env, st, SContinue
    | Some e ->
      let st, signal, init_val = eval_expr ctrl env st SContinue e in
      match signal with
      | SContinue ->
         let st = State.insert_heap l init_val st in
         EvalEnv.insert_val_bare name l env, st, SContinue
      | signal -> env, st, signal

  and eval_set_decl (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (name : string) (size : Expression.t) : env * state * signal =
    let env = EvalEnv.insert_typ_bare name typ env in
    let (st, s, size') = eval_expr ctrl env st SContinue size in
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
        let env = EvalEnv.insert_val_bare name l env in
        (env, st, s)
    | SReject _ -> (env, st, s)
    | _ -> failwith "value set declaration should not return or exit"

  and eval_action_decl (env : env) (st : state) (name : string)
      (data_params : Parameter.t list) (ctrl_params : Parameter.t list)
      (body : Block.t) : env * state =
    let l = State.fresh_loc () in
    let st = State.insert_heap l
      (VAction{scope=env; params = data_params @ ctrl_params; body}) st in
    EvalEnv.insert_val_bare name l env, st

  and eval_table_decl (ctrl : ctrl) (env : env) (st : state) (name : string)
      (key : Table.key list) (actions : Table.action_ref list)
      (entries : (Table.entry list) option) (default : Table.action_ref option)
      (size : P4Int.t option) (props : Table.property list) : env * state =
    let ctrl_default = match List.Assoc.find (snd (fst ctrl)) name ~equal:String.(=) with
                       | None -> default
                       | Some actions' -> Some (convert_action env st   actions (List.hd_exn actions')) in
    let v = VTable { name = name;
                    keys = key;
                    actions = actions;
                    default_action = default_of_defaults ctrl_default;
                    const_entries = entries; } in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    (EvalEnv.insert_val_bare name l env, st)

  and eval_senum_decl (ctrl : ctrl) (env : env) (st : state) (name : string)
      (ms : (P4String.t * Expression.t) list) : env * state =
    let ((st,_),es) = List.fold_map ms ~init:(st,SContinue)
      ~f:(fun (st,s) (n,e) -> let (st,s,v) = eval_expr ctrl env st s e in (st,s), (snd n,v)) in
    let v = VSenum es in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    EvalEnv.insert_val_bare name l env, st

  and eval_extern_obj (env : env) (st : state) (name : string)
      (methods : MethodPrototype.t list) : env * state =
    let v = let open MethodPrototype in methods
      |> List.map ~f:snd
      |> List.map ~f:(function Constructor {name; params;_}
          | AbstractMethod {name; params; _}
          | Method {name; params; _} -> snd name, params ) in
    let l = State.fresh_loc () in
    let st = State.insert_heap l (VExternObj v) st in
    let env = EvalEnv.insert_val_bare name l env in
    env, st

  and eval_pkgtyp_decl (env : env) (st : state) (name : string)
      (params : Parameter.t list) : env * state =
    let v = VPackage {params; args = []} in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    EvalEnv.insert_val_bare name l env, st

  (* -------------------------------------------------------------------------- *)
  (* Table Declaration Evaluation *)
  (* -------------------------------------------------------------------------- *)

  and default_of_defaults (p : Table.action_ref option) : Table.action_ref =
    match p with
      | None -> Info.dummy,
        Table.{ action = {
                  annotations = [];
                  name = BareName (Info.dummy, "NoAction");
                  args = [] };
                typ = Action { data_params = []; ctrl_params = []}}
      | Some action -> action

  and match_params_to_args (params : Parameter.t list) args : (Ast.number * Typed.Type.t) option list =
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
  
  and convert_expression (env : env) (s : (Ast.number * Typed.Type.t) option) : Expression.t option =
    let replace_wildcard s =
      String.map s ~f:(fun c -> if Char.(c = '*') then '0' else c) in
    match s with
    | None -> None
    | Some (s, t) ->
      let num = s |> replace_wildcard |> int_of_string |> Bigint.of_int in
      let rec pre_expr_of_typ env (t : Type.t) =
        match t with
        | Integer -> Expression.Int (Info.dummy, {value = num; width_signed = None})
        | Int {width} -> Expression.Int (Info.dummy, {value = num; width_signed = Some (width,true)})
        | Bit {width} -> Expression.Int (Info.dummy, {value = num; width_signed = Some (width,false)})
        | Bool -> Expression.Int (Info.dummy, {value = num; width_signed = None})
        | TypeName n -> pre_expr_of_typ env (EvalEnv.find_typ n env)
        | _ -> failwith "unsupported type" in
      let pre_exp = pre_expr_of_typ env t in
      let typed_exp : Expression.typed_t = {expr = pre_exp; typ = t; dir = Directionless} in
      let exp = (Info.dummy, typed_exp) in
      if String.contains s '*'
      then begin
      let pre_exp' = Expression.Mask {expr = exp; mask = exp} in
      let typed_exp' : Expression.typed_t = {expr = pre_exp'; typ = Void; dir = Directionless} in
      Some (Info.dummy, typed_exp') end
      else Some exp
  
  and convert_action env st actions (name, args) =
      let action_name' = Types.BareName (Info.dummy, name) in
      let action_type = EvalEnv.find_val action_name' env in
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

  and create_pre_entries env st actions (key: Table.key list) add =
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
        let typed_mask : Expression.typed_t =
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
    (entries : Table.pre_entry list) : Table.pre_entry list =
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
      (stm : Statement.t) : (env * state * signal) =
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
    | DeclarationStatement{decl}      -> eval_declaration_stm ctrl env st sign decl

  and eval_method_call (ctrl : ctrl) (env : env) (st : state) (sign : signal)
      (func : Expression.t) (targs : Type.t list)
      (args : Expression.t option list) : env * state * signal =
    match sign with
    | SContinue -> let (s,i,_) = eval_funcall ctrl env st func targs args in (env,s,i)
    | SReject _ | SReturn _ | SExit -> env, st, sign

  and eval_assign (ctrl : ctrl) (env : env) (st : state) (s : signal) (lhs : Expression.t)
      (rhs : Expression.t) : env * state * signal =
    match s with
    | SContinue ->
      let (st, s', v) = eval_expr ctrl env st SContinue rhs in
      let (st, s'', lv) = lvalue_of_expr ctrl env st s lhs in
      begin match s',s'', lv with
        | SContinue, SContinue, Some lv -> let (st, s) = assign_lvalue st env lv v in env, st, s
        | SContinue, _, _               -> env, st, s''
        | _, _, _                       -> env, st, s'
      end
    | SReject _
    | SReturn _
    | SExit     -> (env, st, s)

  and eval_app (ctrl : ctrl) (env : env) (st : state) (s : signal) (v : value)
    (args : Expression.t option list) : state * signal * value =
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

  and eval_table (ctrl : ctrl) (env : env) (st : state) (key : Table.key list)
      (entries : Table.entry list option)
      (name : string) (actions : Table.action_ref list)
      (default : Table.action_ref) : state * signal * value =
    Printf.printf "Looking up entries for %s\n" name;
    let ctrl_entries = match List.Assoc.find (fst (fst ctrl)) name ~equal:String.(=) with
      | None ->
         Printf.printf "Not found\n%!";
         []
      | Some entries ->
         Printf.printf "Found!!\n%!";
         create_pre_entries env st actions key entries in
    let entries' = match entries with
                        | None -> ctrl_entries
                        | Some entries -> entries |> List.map ~f:snd in
    let entries = sort_priority ctrl env st entries' in
    let key = List.map key ~f:snd in
    let ks = key |> List.map ~f:(fun k -> k.key) in
    let mks = key |> List.map ~f:(fun k -> k.match_kind |> snd) in
    let ((st',s), ks') = List.fold_map ks ~init:(st, SContinue)
        ~f:(fun (b, c) k ->
            let x,y,z = eval_expr ctrl env b c k in ((x,y),z)) in
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
    let action_value = EvalEnv.find_val action_name env |> extract_from_state st'' in
    let args = Table.((snd action).action.args) in
    match action_value with
    | VAction{scope;params;body}  ->
      let (st''',s,_) = eval_funcall' ctrl env st'' scope params args body in
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

  and filter_lpm_prod (st : state) (env : env) (mks : string list) (ks : value list)
      (entries : (set * Table.action_ref) list)
      : (set * Table.action_ref) list * (value list) =
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

  and sort_lpm (entries : (set * Table.action_ref) list)
      : (set * Table.action_ref) list =
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

  and lpm_set_of_set (s : set) : set =
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
      (args : Expression.t list) (t : Type.t) : env * state * signal =
    let (st', sign', v) = eval_nameless ctrl env st t  [] in
    let typname = name_only (name_of_type_ref t) in
    let args' = List.map ~f:(fun arg -> Some arg) args in
    let env'' = EvalEnv.set_namespace (EvalEnv.get_namespace env ^ typname) env in
    let (st'', sign'', _) = eval_app ctrl env'' st' sign' v args' in
    (EvalEnv.set_namespace (EvalEnv.get_namespace env) env'', st'', sign'')

  and eval_cond (ctrl : ctrl) (env : env) (st : state) (sign : signal) (cond : Expression.t)
      (tru : Statement.t) (fls : Statement.t option) : env * state * signal =
    let eval_cond' env cond tru fls =
      let (st', s', v) = eval_expr ctrl env st SContinue cond in
      match s' with
      | SReject _ -> (env, st', s')
      | SContinue ->
        begin match v with
          | VBool true  ->
            tru
            |> eval_stmt ctrl (EvalEnv.push_scope env) st' SContinue
            |> Tuple.T3.map_fst ~f:(fun _ -> env)
          | VBool false ->
            begin match fls with
              | None -> (env, st', SContinue)
              | Some fls' ->
                fls'
                |> eval_stmt ctrl (EvalEnv.push_scope env) st' SContinue
                |> Tuple.T3.map_fst ~f:(fun _ -> env)
            end
          | _ -> failwith "conditional guard must be a bool" end
      | _ -> failwith "unreachable" in
    match sign with
    | SContinue -> eval_cond' env cond tru fls
    | SReject _ | SReturn _ | SExit -> (env, st, sign)

  and eval_block (ctrl : ctrl) (env : env) (st : state) (sign :signal)
      (block : Block.t) : (env * state * signal) =
    let block = snd block in
    let f (env,st,sign) stm =
      match sign with
      | SContinue -> eval_stmt ctrl env st sign stm
      | SReject _ | SReturn _ | SExit -> (env, st, sign) in
    block.statements
    |> List.fold_left ~init:(EvalEnv.push_scope env,st,sign) ~f:f
    |> Tuple.T3.map_fst ~f:(fun _ -> env)

  and eval_exit (env : env) (st : state) (sign : signal) : (env * state * signal) =
    match sign with
    | SContinue -> (env, st, SExit)
    | SReturn v -> (env, st, SReturn v)
    | SExit -> (env, st, SExit)
    | SReject _ -> failwith "reject and exit in the same block"

  and eval_return (ctrl : ctrl) (env : env) (st : state) (sign : signal)
      (expr : Expression.t option) : env * state * signal =
    let (st', s', v) =
      match expr with
      | None   -> (st, SContinue, VNull)
      | Some e -> eval_expr ctrl env st SContinue e in
    match sign with
    | SReject _ | SReturn _ | SExit -> (env,st,sign)
    | SContinue -> begin match s' with
      | SContinue -> (env, st', SReturn v)
      | SReject _ -> (env, st', s')
      | SReturn _ | SExit -> failwith "unreachable" end

  and eval_switch (ctrl : ctrl) (env : env) (st : state) (sign : signal) (expr : Expression.t)
      (cases : Statement.switch_case list) : env * state * signal =
    let open Statement in
    let (st',s',v) = eval_expr ctrl env st SContinue expr in
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
      (decl : Declaration.t) : env * state * signal =
    match sign with
    | SReject _ | SReturn _ | SExit -> (env, st, sign)
    | SContinue ->
      let (env, st) = eval_declaration ctrl env st decl in
      env, st, SContinue

  (*----------------------------------------------------------------------------*)
  (* Functions on L-Values*)
  (*----------------------------------------------------------------------------*)

  and lvalue_of_expr (ctrl : ctrl) (env : env) (st : state) (signal : signal)
      (expr : Expression.t) : state * signal * lvalue option =
    match signal with
    | SContinue -> begin match (snd expr).expr with
      | Name name -> st, SContinue, Some {lvalue = LName {name}; typ = (snd expr).typ}
      | ExpressionMember{expr=e; name=(_,n)} -> lvalue_of_expr_mem ctrl env st (snd expr).typ e n
      | BitStringAccess{bits;lo;hi} -> lvalue_of_expr_bsa ctrl env st (snd expr).typ bits lo hi
      | ArrayAccess{array=a;index} -> lvalue_of_expr_ara ctrl env st (snd expr).typ a index
      | _ -> st, signal, None end
    | SReject _ | SExit | SReturn _ -> st, signal, None

  and lvalue_of_expr_mem (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (e : Expression.t) (n : string) : state * signal * lvalue option =
    let (st', signal, lv) = lvalue_of_expr ctrl env st SContinue e in
    st', signal,
    lv >>| fun lv -> {lvalue = LMember {expr = lv; name = n}; typ }

  and lvalue_of_expr_bsa (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (n : Expression.t) (lsb : Bigint.t)
      (msb : Bigint.t) : state * signal * lvalue option =
    let (st', signal, lv) = lvalue_of_expr ctrl env st SContinue n in
    match signal with
    | SReject _ | SExit | SReturn _ -> st', signal, lv
    | SContinue ->
      st', signal,
      lv >>| fun lv -> {lvalue = LBitAccess{expr=lv; msb = msb; lsb = lsb}; typ}

  and lvalue_of_expr_ara (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (a : Expression.t) (idx : Expression.t) : state * signal * lvalue option =
    let (st', s, lv) = lvalue_of_expr ctrl env st SContinue a in
    let (st'', s', idx') = eval_expr ctrl env st' SContinue idx in
    match s, s' with
    | SContinue, SContinue ->
      st'', s',
      lv >>| fun lv -> {lvalue = LArrayAccess{expr=lv; idx=idx'}; typ }
    | SContinue, _ -> st'', s', lv
    | _, _ -> st', s, lv

  (*----------------------------------------------------------------------------*)
  (* Expression Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_expr (ctrl : ctrl) (env : env) (st : state) (s : signal)
      (exp : Expression.t) : state * signal * value =
    match s with
    | SContinue ->
      begin match (snd exp).expr with
        | True                              -> (st, s, VBool true)
        | False                             -> (st, s, VBool false)
        | Int(_,n)                          -> (st, s, eval_p4int n)
        | String (_,value)                  -> (st, s, VString value)
        | Name name                         -> eval_name env st name exp
        | ArrayAccess{array=a; index=i}     -> eval_array_access ctrl env st a i
        | BitStringAccess({bits;lo;hi})     -> eval_bitstring_access ctrl env st bits hi lo
        | Record{entries}                   -> eval_record ctrl env st entries
        | List{values}                      -> eval_list ctrl env st values
        | UnaryOp{op;arg}                   -> eval_unary ctrl env st op arg
        | BinaryOp{op; args=(l,r)}          -> eval_binop ctrl env st op l r
        | Cast{typ;expr}                    -> eval_cast ctrl env st typ expr
        | TypeMember{typ;name}              -> eval_typ_mem ctrl env st typ (snd name)
        | ErrorMember t                     -> (st, s, VError (snd t))
        | ExpressionMember{expr;name}       -> eval_expr_mem ctrl env st expr name
        | Ternary{cond;tru;fls}             -> eval_ternary ctrl env st cond tru fls
        | FunctionCall{func;args;type_args} -> eval_funcall ctrl env st func type_args args
        | NamelessInstantiation{typ;args}   -> eval_nameless ctrl env st typ args
        | Mask{expr;mask}                   -> eval_mask ctrl env st expr mask
        | Range{lo;hi}                      -> eval_range ctrl env st lo hi
        | DontCare                          -> st, s, VNull end
    | SReject _ -> (st, s, VNull)
    | SReturn _ -> failwith "expression should not return"
    | SExit -> failwith "expresion should not exit"

  and eval_name (env : env) (st : state) (name : Types.name)
      (exp : Expression.t) : state * signal * value =
    let s = SContinue in
    (st, s, EvalEnv.find_val name env |> extract_from_state st)

  and eval_p4int (n : P4Int.pre_t) : value =
    match n.width_signed with
    | None          -> VInteger n.value
    | Some(w,true)  -> VInt {w=Bigint.of_int w;v=n.value}
    | Some(w,false) -> VBit {w=Bigint.of_int w;v=n.value}

  and eval_array_access (ctrl : ctrl) (env : env) (st : state) (a : Expression.t)
      (i : Expression.t) : state * signal * value =
    let (st', s, a') = eval_expr ctrl env st SContinue a in
    let (st'', s', i') = eval_expr ctrl env st' SContinue i in
    let idx = bigint_of_val i' in
    let (hdrs,size,next) = assert_stack a' in
    let idx' = Bigint.(to_int_exn (idx % size)) in
    let v = List.nth_exn hdrs idx' in
    match (s,s') with
    | SContinue, SContinue -> (st'', SContinue, v)
    | SReject _,_ -> (st',s, VNull)
    | _,SReject _ -> (st'',s',VNull)
    | _ -> failwith "unreachable"

  and eval_bitstring_access (ctrl : ctrl) (env : env) (st : state) (b : Expression.t)
      (m : Bigint.t) (l : Bigint.t) : state * signal * value =
    let (st', s, b) = eval_expr ctrl env st SContinue b in
    let b' = bigint_of_val b in
    let w = Bigint.(m-l + one) in
    let n = bitstring_slice b' m l in
    match s with
    | SContinue -> (st', SContinue, VBit{w;v=n})
    | SReject _ | SExit | SReturn _ -> (st',s,VNull)

  and eval_record (ctrl : ctrl) (env : env) (st : state)
      (kvs : KeyValue.t list) : state * signal * value =
    let es = List.map kvs ~f:(fun kv -> (snd kv).value) in
    let ks = List.map kvs ~f:(fun kv -> snd (snd kv).key) in
    let f (b,c) d =
      let (x,y,z) = eval_expr ctrl env b c d in
      ((x,y),z) in
    es
    |> List.fold_map ~f:f ~init:(st, SContinue)
    |> (fun ((st,s),l) -> st,s, VRecord (List.zip_exn ks l))

  and eval_list (ctrl : ctrl) (env : env) (st : state)
      (values : Expression.t list) : state * signal * value =
    let f (b,c) d =
      let (x,y,z) = eval_expr ctrl env b c d in
      ((x,y),z) in
    values
    |> List.fold_map ~f:f ~init:(st,SContinue)
    |> (fun ((st,s),l) -> (st, s, VTuple l))

  and eval_unary (ctrl : ctrl) (env : env) (st : state) (op : Op.uni)
      (e : Expression.t) : state * signal * value =
    let (st', s, v) = eval_expr ctrl env st SContinue e in
    match s with
    | SContinue ->
       let v = Ops.interp_unary_op op v in
      (st', s,v)
    | SReject _ -> (st',s,VNull)
    | _ -> failwith "unreachable"

  and eval_binop (ctrl : ctrl) (env : env) (st : state) (op : Op.bin) (l : Expression.t)
      (r : Expression.t) : state * signal * value =
    let shortcircuit env st l r f =
      let st, s, l = eval_expr ctrl env st SContinue l in
      match s with SReject _ | SReturn _ | SExit -> st, s, VNull
      | SContinue ->
        if l |> assert_bool |> f
        then st, s, l
        else eval_expr ctrl env st SContinue r in
    match snd op with
    | And -> shortcircuit env st l r not
    | Or -> shortcircuit env st l r ident
    | _ ->
      let (st',s,l) = eval_expr ctrl env st SContinue l in
      let (st'',s',r) = eval_expr ctrl env st' SContinue r in
      let v = Ops.interp_binary_op op l r in
      begin match (s,s') with
        | SContinue, SContinue -> (st'', SContinue, v)
        | SReject _,_ -> (st',s,VNull)
        | _,SReject _ -> (st'',s',VNull)
        | _ -> failwith "unreachable"
      end

  and eval_cast (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (expr : Expression.t) : state * signal * value =
    let (st', s, v) = eval_expr ctrl env st SContinue expr in
    let v' = Ops.interp_cast typ v
      ~type_lookup:(fun name -> EvalEnv.find_typ name env) in
    match s with
    | SContinue -> (st',s,v')
    | _ -> (st',s,VNull)

  and eval_typ_mem (ctrl : ctrl) (env : env) (st : state) (typ : Types.name)
      (enum_name : string) : state * signal * value =
    match EvalEnv.find_typ typ env with
    | Enum {name; typ = None; members} ->
      if List.mem members enum_name ~equal:String.equal
      then (st, SContinue, VEnumField{typ_name=name;enum_name})
      else raise (UnboundName name)
    | Enum {name; typ = Some _; members} ->
      begin match EvalEnv.find_val typ env |> extract_from_state st with
        | VSenum fs ->
          let v = find_exn fs enum_name in
          st, SContinue, VSenumField{typ_name=name;enum_name;v}
        | _ -> failwith "typ mem undefined"
      end
    | _ -> failwith "type mem undefined"

  and eval_expr_mem (ctrl : ctrl) (env : env) (st : state) (expr : Expression.t)
      (name : P4String.t) : state * signal * value =
    let (st', s, v) = eval_expr ctrl env st SContinue expr in
    let third3 (_,_,x) = x in
    match s with
    | SContinue ->
      begin match v with
        | VStruct{fields=fs} ->
          eval_struct_mem env st' (snd name) fs
        | VHeader{fields=fs;is_valid=vbit} ->
          eval_header_mem ctrl env st' (snd name) expr fs vbit
        | VUnion{fields=fs} ->
          eval_union_mem ctrl env st' (snd name) expr fs
        | VStack{headers=hdrs;size=s;next=n} ->
          eval_stack_mem ctrl env st' (snd name) expr hdrs s n
        | VRuntime {loc; obj_name} ->
          eval_runtime_mem env st' (snd name) expr loc obj_name
        | VRecord fs ->
          st', s, find_exn fs (snd name)
        | VParser _ | VControl _ | VTable _ ->
          let name = snd name in
          let caller = lvalue_of_expr ctrl env st' SContinue expr
            |> third3
            |> Option.value_exn in
          st', s, VBuiltinFun { name; caller; }
        | _ -> failwith "type member does not exists"
      end
    | SReject _ -> (st',s,VNull)
    | _ -> failwith "unreachable"

  and eval_ternary (ctrl : ctrl) (env : env) (st : state) (c : Expression.t)
      (te : Expression.t) (fe : Expression.t) : state * signal * value =
    let (st', s, c') = eval_expr ctrl env st SContinue c in
    match c' with
    | VBool(true)  -> (eval_expr ctrl env st' s te)
    | VBool(false) -> (eval_expr ctrl env st' s fe)
    | _ -> failwith "ternary guard must be a bool"

  and eval_funcall (ctrl : ctrl) (env : env) (st : state) (func : Expression.t)
      (targs : Type.t list)
      (args : Expression.t option list) : state * signal * value =
    let (st', s, cl) = eval_expr ctrl env st SContinue func in
    match s with
    | SContinue -> begin match cl with
      | VAction{scope;params; body} | VFun{scope;params; body} ->
        eval_funcall' ctrl env st' scope params args body
      | VBuiltinFun{name=n;caller=lv} ->
        eval_builtin ctrl env st' n lv args
      | VExternFun{name=n;caller=v;params} ->
        eval_extern_call ctrl env st' n v params targs args
      | _ -> failwith "unreachable" end
    | SReject _ -> (st',s,VNull)
    | _ -> failwith "unreachable"

  and eval_nameless (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (args : Expression.t list) : state * signal * value =
    let name = name_of_type_ref typ in
    let args' = List.map ~f:(fun arg -> Some arg) args in
    match EvalEnv.find_val name env |> extract_from_state st with
    | VPackage {params;_} ->
      let (_, env,st,s) = (env --> env) ctrl st params args' in
      let args = env |> EvalEnv.get_val_firstlevel |> List.rev in
      (st, s, VPackage{params;args;})
    | VControl {cscope;cconstructor_params;cparams;clocals;apply} ->
      let (_, cscope,st,s) = (env --> cscope) ctrl st cconstructor_params args' in
      let v = VControl { cscope; cconstructor_params; cparams; clocals; apply; } in
      (st,s,v)
    | VParser {pscope;pconstructor_params;pparams;plocals;states} ->
      let (_, pscope,st,s) = (env --> pscope) ctrl st pconstructor_params args' in
      let v = VParser {pscope; pconstructor_params; pparams; plocals; states; } in
      (st,s,v)
    | VExternObj ps ->
      let loc = EvalEnv.get_namespace env in
      if State.is_initialized loc st
      then st, SContinue, VRuntime {loc = loc; obj_name = name_only name; }
      else 
        let params = List.Assoc.find_exn ps (name_only name) ~equal:String.equal in
        eval_extern_call ctrl env st (name_only name) (Some (loc, name_only name)) params [] args'
    | _ -> failwith "instantiation unimplemented"

  and eval_mask (ctrl : ctrl) (env : env) (st : state) (e : Expression.t)
      (m : Expression.t) : state * signal * value =
    let (st', s, v1)  = eval_expr ctrl env st SContinue e in
    let (st'', s', v2) = eval_expr ctrl env st' SContinue m in
    match (s,s') with
    | SContinue, SContinue ->
      (st'', s, VSet(SMask{v=v1;mask=v2}))
    | SReject _,_ -> (st',s,VNull)
    | _,SReject _ -> (st'',s',VNull)
    | _ -> failwith "unreachable"

  and eval_range (ctrl : ctrl) (env : env) (st : state) (lo : Expression.t)
      (hi : Expression.t) : state * signal * value =
    let (st', s, v1) = eval_expr ctrl env st SContinue lo in
    let (st'',s',v2) = eval_expr ctrl env st' SContinue hi in
    match (s,s') with
    | SContinue, SContinue -> (st'', s, VSet(SRange{lo=v1;hi=v2}))
    | SReject _,_ -> (st',s,VNull)
    | _,SReject _ -> (st'',s',VNull)
    | _ -> failwith "unreachable"

  (*----------------------------------------------------------------------------*)
  (* Membership Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_struct_mem (env : env) (st : state) (name : string)
      (fs : (string * value) list) : state * signal * value =
    (st, SContinue, (find_exn fs name))

  and eval_header_mem (ctrl : ctrl) (env : env) (st : state) (fname : string)
      (e : Expression.t) (fs : (string * value) list)
      (valid : bool) : state * signal * value =
    match fname with
    | "setValid" | "setInvalid" ->
      let (_, _, lv) = lvalue_of_expr ctrl env st SContinue e in
      st, SContinue, VBuiltinFun{name=fname;caller=Option.value_exn lv}
    | "isValid" -> begin try
      let (_, _, lv) = lvalue_of_expr ctrl env st SContinue e in
      st, SContinue, VBuiltinFun{name=fname; caller=Option.value_exn lv}
      with _ -> failwith "TODO: edge case with header isValid()" end
    | _ -> (st, SContinue, T.read_header_field valid fs fname)

  and eval_union_mem (ctrl : ctrl) (env : env) (st : state)
    (fname : string) (e : Expression.t) (fs : (string * value) list)
    : state * signal * value =
    let (st', signal, lv) = lvalue_of_expr ctrl env st SContinue e in
    match fname with
    | "isValid" -> begin match signal, lv with
      | SContinue, Some lv -> st', SContinue, VBuiltinFun{name=fname;caller=lv}
      | _, _ -> st', signal, VNull end
    | _ -> (st, SContinue, (find_exn fs fname))

  and eval_stack_mem (ctrl : ctrl) (env : env) (st : state) (fname : string)
      (e : Expression.t) (hdrs : value list) (size : Bigint.t)
      (next : Bigint.t) : state * signal * value =
    match fname with
    | "size" -> eval_stack_size env st size
    | "next" -> eval_stack_next env st hdrs size next
    | "last" -> eval_stack_last env st hdrs size next
    | "lastIndex" -> eval_stack_lastindex env st next
    | "pop_front" | "push_front" ->
      eval_stack_builtin ctrl env st fname e
    | _ -> failwith "stack member unimplemented"

  and eval_runtime_mem (env : env) (st : state) (mname : string) (expr : Expression.t)
      (loc : loc) (obj_name : string) : state * signal * value =
    let params = EvalEnv.find_val (BareName (Info.dummy, obj_name)) env
      |> (fun l -> State.find_heap l st)
      |> assert_externobj
      |> fun l -> List.Assoc.find_exn l mname ~equal:String.equal in
    st, SContinue, VExternFun {caller = Some (loc, obj_name); name = mname; params }

  and eval_stack_size (env : env) (st : state)
      (size : Bigint.t) : state * signal * value =
    let five = Bigint.(one + one + one + one + one) in
    let thirty_two = shift_bitstring_left Bigint.one five in
    (st, SContinue, VBit{w=thirty_two;v=size})

  and eval_stack_next (env : env) (st : state) (hdrs : value list) (size : Bigint.t)
      (next : Bigint.t) : state * signal * value =
    if Bigint.(next >= size)
    then st, SReject "StackOutOfBounds", VNull
    else st, SContinue, List.nth_exn hdrs Bigint.(to_int_exn next)

  and eval_stack_last (env : env) (st : state) (hdrs : value list) (size : Bigint.t)
      (next : Bigint.t) : state * signal *  value =
    if Bigint.(next < one) || Bigint.(next > size)
    then st, SReject "StackOutOfBounds", VNull
    else st, SContinue, List.nth_exn hdrs Bigint.(to_int_exn (next - one))

  and eval_stack_lastindex (env : env) (st : state)
      (next : Bigint.t) : state * signal * value =
    st, SContinue, Bigint.(VBit {w= of_int 32; v= next - one})

  and eval_stack_builtin (ctrl : ctrl) (env : env) (st : state) (name : string)
      (e : Expression.t) : state * signal * value =
    let (st', signal, lv) = lvalue_of_expr ctrl env st SContinue e in
    st', signal, VBuiltinFun{name; caller = Option.value_exn lv}

  (*----------------------------------------------------------------------------*)
  (* Function and Method Call Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_extern_call (ctrl : ctrl) (callenv : env) (st : state) (name : string)
      (v : (loc * string) option) (params : Parameter.t list) (targs : Type.t list)
      (args : Expression.t option list) : state * signal * value =
    let ts = args |> List.map ~f:(function Some e -> (snd e).typ | None -> Void) in
    let params =
      match v with
      | Some (_,t) ->
        EvalEnv.find_val (BareName (Info.dummy, t)) callenv
        |> extract_from_state st
        |> assert_externobj
        |> List.filter ~f:(fun (s,_) -> String.equal s name)
        |> List.filter ~f:(fun (_,ps) -> Int.equal (List.length ps) (List.length args))
        |> List.hd_exn
        |> snd
      | None ->
        EvalEnv.find_val (BareName (Info.dummy, name)) callenv
        |> extract_from_state st
        |> assert_externfun in
    let (_,kvs) =
      List.fold_mapi args ~f:(eval_nth_arg ctrl callenv st params) ~init:([], st,SContinue) in
    let (lvs, fenv, st', signal) = (callenv --> callenv) ctrl st params args in
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

  and eval_funcall' (ctrl : ctrl) (callenv : env) (st : state) (fscope : env)
      (params : Parameter.t list) (args : Expression.t option list)
      (body : Block.t) : state * signal * value =
    let (lvs, fenv, st', s) = (callenv --> fscope) ctrl st params args in
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
  and (-->) (callenv : env) (fscope : env) : ctrl -> state -> Parameter.t list ->
      Expression.t option list -> lvalue option list * env * state * signal = fun ctrl st params args ->
    let fenv = EvalEnv.push_scope fscope in
    let f = eval_nth_arg ctrl callenv st params in
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
  and (<--) (callenv:env) (fenv : env) : state -> Parameter.t list ->
      lvalue option list -> state = fun st ->
    List.fold2_exn ~init:st ~f:(copy_arg_out fenv callenv)

  and eval_nth_arg (ctrl : ctrl) (env : env) (st : state) (params : Parameter.t list) (i : int)
      (lvs, st, sign : lvalue option list * state * signal)
      (e : Expression.t option) : (lvalue option list * state * signal) * (string * value) =
    let p = List.nth_exn params i in
    let ((st',s,lv), n) = match e with
      | Some expr -> lvalue_of_expr ctrl env st SContinue expr, snd p.variable
      | None -> (st, SContinue, None), snd p.variable in
    let (st', s, v) = match lv with
      | Some lv -> st', s, value_of_lvalue env st' lv |> snd
      | None -> begin match e with
        | Some expr -> eval_expr ctrl env st SContinue expr
        | None -> (st, SContinue, VNull) end in
    match (sign,s) with
    | SContinue, SContinue -> (lv :: lvs, st', s), (n, v)
    | SReject _, _ -> (lv :: lvs, st, sign), (n, VNull)
    | _, SReject _ -> (lv :: lvs, st', s), (n, VNull)
    | _ -> failwith "unreachable"

  and insert_arg (e, st : EvalEnv.t * state) (p : Parameter.t)
      (name, v : string * value) : env * state =
    (* TODO: zero out v if dir = out *)
    let var = Types.BareName p.variable in
    let l = State.fresh_loc () in
    let st = State.insert_heap l v st in
    EvalEnv.insert_val var l e, st

  and copy_arg_out (fenv : env) (callenv : env) (st : state) (p : Parameter.t)
      (a : lvalue option) : state =
    match p.direction with
    | InOut | Out -> copy_arg_out_h fenv st callenv p a
    | In | Directionless -> st

  and copy_arg_out_h (fenv : env) (st : state)
      (callenv : env) (p : Parameter.t) (lv : lvalue option) : state =
    let v = EvalEnv.find_val (BareName p.variable) fenv |> extract_from_state st in
    match lv with
    | None -> st
    | Some lv -> assign_lvalue st callenv lv v |> fst

  (*----------------------------------------------------------------------------*)
  (* Built-in Function Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_builtin (ctrl :ctrl) (env : env) (st : state) (name : string) (lv : lvalue)
      (args : Expression.t option list) : state * signal * value =
    match name with
    | "isValid"    -> eval_isvalid env st lv
    | "setValid"   -> eval_setbool env st lv true
    | "setInvalid" -> eval_setbool env st lv false
    | "pop_front"  -> eval_push_pop ctrl env st lv args false
    | "push_front" -> eval_push_pop ctrl env st lv args true
    | "apply" ->
      let lvname = match lv.lvalue with
        | LName {name} -> name
        | _ -> failwith "bad apply" in
      let (s,v) = value_of_lvalue env st lv in
      eval_app ctrl (EvalEnv.set_namespace (name_only lvname) env) st s v args
    | _ -> failwith "builtin unimplemented"

  and eval_isvalid (env : env) (st : state)
      (lv : lvalue) : state * signal * value =
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

  and eval_setbool (env : env) (st : state) (lv : lvalue)
      (b : bool) : state * signal * value =
    let (s,v) = value_of_lvalue env st lv in
    match s, v with
    | (SReturn _ | SExit | SReject _), _ -> (st, s, VNull)
    | SContinue, VHeader hdr ->
       let st, signal = assign_lvalue st env lv (VHeader {hdr with is_valid = b}) in
       (st, signal, VBool b)
    | SContinue, _ ->
       failwith "isvalid call is not a header"

  and eval_push_pop (ctrl : ctrl) (env : env) (st : state) (lv : lvalue)
      (args : Expression.t option list) (b : bool) : state * signal * value =
    let (st', s, a) = eval_push_pop_args ctrl env st args in
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

  and eval_push_pop_args (ctrl : ctrl) (env : env) (st : state)
      (args : Expression.t option list) : state * signal * Bigint.t =
    match args with
    | [Some value] ->
      let (st', s, v) = eval_expr ctrl env st SContinue value in
      begin match s with
        | SContinue -> (st', s, bigint_of_val v)
        | SReject _ -> (st', s, Bigint.zero)
        | _ -> failwith "unreachable" end
    | _ -> failwith "invalid push or pop args"

  (*----------------------------------------------------------------------------*)
  (* Parser Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_parser (ctrl : ctrl) (env : env) (st : state) (params : Parameter.t list)
      (args : Expression.t option list) (pscope : env)
      (locals : Declaration.t list) (states : Parser.state list) : state * signal =
    let (lvs, penv, st, s) = (env --> pscope) ctrl st params args in
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
      (states : (string * Parser.state) list)
      (state : Parser.state) : env * state * signal =
    let () = Printf.eprintf "Parser: %s\n%!" (snd (snd state).name) in
    let (stms, transition) =
      match snd state with
      | {statements=stms; transition=t;_} -> (stms, t) in
    let f (env, st, sign) stm =
      match sign with
      | SContinue -> eval_stmt ctrl env st sign stm
      | _ -> (env, st, sign) in
    let (env', st', sign) = List.fold ~f ~init:(EvalEnv.push_scope env,st, SContinue) stms in
    match sign with
    | SContinue ->
      eval_transition ctrl env' st' states transition
      |> Tuple.T3.map_fst ~f:EvalEnv.pop_scope
    | SReject _ -> (env', st', sign)
    | SReturn _ -> failwith "return statements not permitted in parsers"
    | SExit -> failwith "exit statements not permitted in parsers"

  and eval_transition (ctrl : ctrl) (env : env) (st : state)
      (states : (string * Parser.state) list)
      (transition : Parser.transition) : env * state * signal =
    match snd transition with
    | Direct{next = (_, next)} -> eval_direct ctrl env st states next
    | Select{exprs;cases} -> eval_select ctrl env st states exprs cases

  and eval_direct (ctrl : ctrl) (env : env) (st : state)
      (states : (string * Parser.state) list) (next : string) : env * state * signal =
    match next with
    | "accept" -> env, st, SContinue
    | "reject" -> env, st, SReject "NoError"
    | _        -> eval_state_machine ctrl env st states (find_exn states next)

  and eval_select (ctrl : ctrl) (env : env) (st : state)
      (states : (string * Parser.state) list) (exprs : Expression.t list)
      (cases : Parser.case list) : env * state * signal =
    let f (st,s) e =
      let (b,c,d) = eval_expr ctrl env st s e in
      ((b,c),d) in
    let ((st', s), vs) = List.fold_map exprs ~init:(st,SContinue) ~f:f in
    let ws = List.map vs ~f:(width_of_val) in
    match s with
    | SContinue ->
      let g (e,st,s) set =
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

  and eval_control (ctrl : ctrl) (env : env) (st : state) (params : Parameter.t list)
      (args : Expression.t option list) (cscope : env)
      (locals : Declaration.t list) (apply : Block.t) : state * signal =
    let open Statement in
    let (lvs, cenv,st,_) = (env --> cscope) ctrl st params args in
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
      (case : Parser.case) (ws : Bigint.t list) : env * state * signal * set =
    match s with
    | SContinue -> set_of_matches ctrl env st s (snd case).matches ws
    | SReject _ -> (env,st,s,SUniversal)
    | _ -> failwith "unreachable"

  and set_of_matches (ctrl : ctrl) (env : env) (st : state) (s : signal)
      (ms : Match.t list) (ws : Bigint.t list) : env * state * signal * set =
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
      (m : Match.t) (w : Bigint.t) : env * state * signal * set =
    match s with
    | SContinue ->
      begin match (snd m).expr with
        | DontCare         -> (env, st, SContinue, SUniversal)
        | Expression{expr} ->
          let (st', s, v) = eval_expr ctrl env st SContinue expr in
          (env, st', s, assert_set v w) end
    | SReject _ -> (env, st, s, SUniversal)
    | _ -> failwith "unreachable"

  and values_match_set (st : state) (vs : value list) (s : set) : bool =
    match s with
    | SSingleton{w;v}     -> values_match_singleton vs v
    | SUniversal          -> true
    | SMask{v=v1;mask=v2} -> values_match_mask st vs v1 v2
    | SRange{lo=v1;hi=v2} -> values_match_range vs v1 v2
    | SProd l             -> values_match_prod st vs l
    | SLpm{w=v1;v=v2;_}   -> values_match_mask st vs v1 v2
    | SValueSet {sets=ss;_}   -> values_match_value_set st vs ss

  and values_match_singleton (vs : value list) (n : Bigint.t) : bool =
    let v = List.hd_exn vs in
    v |> bigint_of_val |> (Bigint.(=) n)

  and values_match_mask (st : state) (vs : value list) (v1 : value)
      (v2 : value) : bool =
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

  and values_match_range (vs : value list) (low_bound : value) (high_bound : value) : bool =
    let v = bigint_of_val (List.hd_exn vs) in
    let low_bound = bigint_of_val low_bound in
    let high_bound = bigint_of_val high_bound in
    Bigint.(low_bound <= v && v <= high_bound)

  and values_match_prod (st : state) (vs : value list) (l : set list) : bool =
    let bs = List.mapi l ~f:(fun i x -> values_match_set st [List.nth_exn vs i] x) in
    List.for_all bs ~f:(fun b -> b)

  and values_match_value_set (st : state) (vs : value list) (l : set list) : bool =
    let bs = List.map l ~f:(values_match_set st vs) in
    List.exists bs ~f:(fun b -> b)

  (*----------------------------------------------------------------------------*)
  (* Helper functions *)
  (*----------------------------------------------------------------------------*)

  and extract_from_state (st : state) (l : loc) : value =
    State.find_heap l st

  and name_only name = 
    match name with Types.BareName s | Types.QualifiedName (_, s) -> snd s

  and label_matches_string (s : string) (case : Statement.pre_switch_case) : bool =
    match case with
    | Action{label;_} | FallThrough{label} -> match snd label with
      | Default -> true
      | Name(_,n) -> String.equal s n

  and name_of_type_ref (typ: Type.t) =
    match typ with
    | TypeName name -> name
    | NewType nt -> BareName (Info.dummy, nt.name)
    | Enum et -> BareName (Info.dummy, et.name)
    | SpecializedType { base; args = _ } ->
        name_of_type_ref base
    | _ -> failwith "can't find name for this type"

  and eval_statement ctrl env st s =
    let (a,b,_) = eval_stmt ctrl env st SContinue s in (a,b)

  and eval_expression ctrl env st expr =
    let (b,_,c) = eval_expr ctrl env st SContinue expr in (b,c)

  and eval
      (ctrl : ctrl)
      (env : env)
      (st : state)
      (pkt : pkt)
      (in_port : Bigint.t)
      (num_ports : Bigint.t) : state * env * (pkt * Bigint.t) list =
    let st = T.initialize_metadata in_port num_ports st in
    let (st, env, pkts) = T.eval_pipeline ctrl env st pkt eval_app in
    st, env, pkts

  and eval_main
      (ctrl : ctrl)
      (env : env)
      (st : state)
      (pkt : pkt)
      (in_port : Bigint.t)
      (num_ports : Bigint.t) : state * (pkt * Bigint.t) list =
    let (st, _, pkts) = eval ctrl env st pkt in_port num_ports in
    st, pkts

  and eval_program (ctrl : ctrl) (env: env) (st : state) (pkt : buf)
      (in_port : Bigint.t) (num_ports : Bigint.t)
      (prog : program) : state * (buf * Bigint.t) list =
    let st = State.reset_state st in
    match prog with Program l ->
    let (env,st) =
      List.fold l
        ~init:(env, st)
        ~f:(fun (e,s) -> eval_declaration ctrl e s)
    in
    let pkt = {emitted = Cstruct.empty; main = pkt; in_size = Cstruct.len pkt} in
    let st, pkts = eval_main ctrl env st pkt in_port num_ports in
    st, List.map pkts
          ~f:(fun (pkt, pt) -> (Cstruct.append pkt.emitted pkt.main, pt))

  let init_switch (env : env) (prog : program) : env * state =
    match prog with Program l ->
    List.fold l ~init:(env, empty_state)
      ~f:(fun (e,s) -> eval_declaration (([], []),[]) e s)

  let switch_packet (ctrl : ctrl) (env : env) (st : state) (pkt : buf)
      (pt : Bigint.t) (num_ports : Bigint.t) : state * (buf * Bigint.t) list =
    let pkt = {emitted = Cstruct.empty; main = pkt; in_size = Cstruct.len pkt} in
    let (st, pkts) = eval_main ctrl env st pkt pt num_ports in
    st, List.map pkts ~f:(fun (pkt, pt) -> (Cstruct.append pkt.emitted pkt.main, pt))

end

(*----------------------------------------------------------------------------*)
(* Program Evaluation *)
(*----------------------------------------------------------------------------*)

module V1Interpreter = MakeInterpreter(V1model.V1Switch)

module EbpfInterpreter = MakeInterpreter(Ebpf.EbpfFilter)

module Up4Interpreter = MakeInterpreter(Up4.Up4Filter)
