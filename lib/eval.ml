module I = Info
open Core
open Env
open Types
open Value
open Value
module Info = I (* JNF: ugly hack *)

(*----------------------------------------------------------------------------*)
(* Declaration Evaluation *)
(*----------------------------------------------------------------------------*)

let rec eval_decl (env : EvalEnv.t) (d : Declaration.t) : EvalEnv.t =
  match snd d with
  | Constant {
      annotations = _;
      typ = t;
      value = v;
      name = (_,n);
    } -> eval_const_decl env t v n
  | Instantiation {
      annotations = _;
      typ = typ;
      args = args;
      name = (_,n);
    } -> eval_instantiation env typ args n
  | Parser {
      annotations = _;
      name = (_,n);
      type_params = _;
      params = _;
      constructor_params = _;
      locals = _;
      states = _;
    } -> eval_parser_decl env n d
  | Control {
      annotations = _;
      name = (_,n);
      type_params = _;
      params = _;
      constructor_params = _;
      locals = _;
      apply = _;
    } -> eval_control_decl env n d
  | Function {
      return = _;
      name = (_,n);
      type_params = _;
      params = ps;
      body = b;
    } -> eval_fun_decl env n ps b d
  | ExternFunction {
      annotations = _;
      return = _;
      name = (_,n);
      type_params = _;
      params = ps;
    } -> eval_extern_fun env n ps d
  | Variable {
      annotations = _;
      typ = t;
      name = (_,n);
      init = v;
    } -> eval_var_decl env t n v |> fst
  | ValueSet {
      annotations = _;
      typ = _;
      size = _;
      name = _;
    } -> eval_set_decl ()
  | Action {
      annotations = _;
      name = (_,n);
      params = ps;
      body = b;
    } -> eval_action_decl env n ps b d
  | Table {
      annotations = _;
      name = (_,n);
      properties = ps;
    } -> eval_table_decl env n d ps
  | Header {
      annotations = _;
      name = (_,n);
      fields = _;
    } -> eval_header_decl env n d
  | HeaderUnion {
      annotations = _;
      name = (_,n);
      fields = _;
    } -> eval_union_decl env n d
  | Struct {
      annotations = _;
      name = (_,n);
      fields = _;
    } -> eval_struct_decl env n d
  | Error {
      members = l;
    } -> eval_error_decl env l
  | MatchKind {
      members = l;
    } -> eval_matchkind_decl env l
  | Enum {
      annotations = _;
      name = (_,n);
      members = _;
    } -> eval_enum_decl env n d
  | SerializableEnum {
      annotations = _;
      typ = _;
      name = (_,n);
      members = _;
    } -> eval_senum_decl env n d
  | ExternObject {
      annotations = _;
      name = (_,n);
      type_params = tps;
      methods = ms;
    } -> eval_extern_obj env n ms d
  | TypeDef {
      annotations = _;
      name = (_,n);
      typ_or_decl = _;
    } -> eval_type_def env n d
  | NewType {
      annotations = _;
      name = (_,n);
      typ_or_decl = _;
    } -> eval_type_decl env n d
  | ControlType {
      annotations = _;
      name = (_,n);
      type_params = _;
      params = _;
    } -> eval_ctrltyp_decl env n d
  | ParserType {
      annotations = _;
      name = (_,n);
      type_params = _;
      params = _;
    } -> eval_prsrtyp_decl env n d
  | PackageType {
      annotations = _;
      name = (_,n);
      type_params = _;
      params = _;
    } -> eval_pkgtyp_decl env n d

and eval_const_decl (env : EvalEnv.t) (typ : Type.t) (e : Expression.t)
    (name : string) : EvalEnv.t =
  let name_expr = (Info.dummy, Expression.Name(Info.dummy, name)) in
  let env' = EvalEnv.insert_typ name typ env in
  fst (eval_assign env' SContinue name_expr e)

and eval_instantiation (env:EvalEnv.t) (typ : Type.t) (args : Argument.t list)
    (name : string) : EvalEnv.t =
  let (env', _,obj) = eval_nameless env typ args in
  EvalEnv.insert_val name obj env'

and eval_parser_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_control_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_fun_decl (env : EvalEnv.t) (name : string) (params : Parameter.t list)
    (body : Block.t) (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_val name (VFun(params,body)) env
  |> EvalEnv.insert_decl name decl

and eval_extern_fun (env : EvalEnv.t) (name : string)
    (params : Parameter.t list) (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_val name (VExternFun params) env
  |> EvalEnv.insert_decl name decl

and eval_var_decl (env : EvalEnv.t) (typ : Type.t) (name : string)
    (init : Expression.t option) : EvalEnv.t * signal =
  let env' = EvalEnv.insert_typ name typ env in
  match init with
  | None ->
    let env'' = EvalEnv.insert_val name (init_val_of_typ env' name typ) env' in
    (env'', SContinue)
  | Some e ->
    let (env'', s, v) = eval_expression' env' SContinue e in
    match s with
    | SContinue -> (EvalEnv.insert_val name v env'', s)
    | SReject -> (env, s)
    | SReturn _ -> failwith "variable declaration should not return"
    | SExit -> failwith "variable declaration should not exit"

and eval_set_decl () = failwith "set decls unimplemented"

and eval_action_decl (env : EvalEnv.t) (name : string) (params : Parameter.t list)
    (body : Block.t) (decl : Declaration.t) : EvalEnv.t  =
  EvalEnv.insert_val name (VAction(params, body)) env
  |> EvalEnv.insert_decl name decl

and eval_table_decl (env : EvalEnv.t) (name : string) (decl : Declaration.t)
    (props : Table.property list) : EvalEnv.t =
  let props' = List.map props ~f:snd in
  let env' = EvalEnv.insert_decl name decl env in
  let ctrl_entries = EvalEnv.get_tables env' in
  let pre_ks = List.filter props' ~f:is_key
               |> List.hd_exn
               |> assert_key
               |> List.map ~f:snd in
  let key = pre_ks |> List.map ~f:(fun k -> k.key) in
  let mks = pre_ks |> List.map ~f:(fun k -> snd k.match_kind) in
  let ((env'',s), ks) = List.fold_map key ~init:(env', SContinue)
      ~f:(fun (a, b) k ->

          let x,y,z = eval_expression' a b k in ((x,y),z)) in
  let f ((w,x,y),z) = ((w,x),(y,z)) in
  let sort_mks = check_lpm mks in
  let ws = List.map ks ~f:width_of_val in
  let ((env''',s'),entries) =
    begin
      match List.filter props' ~f:is_entries with
      | [] -> List.fold_map ctrl_entries ~init:(env'',s)
                ~f:(fun (a,b) c -> (set_of_matches a b c.matches ws, c.action) |> f)
      | l -> l
             |> List.hd_exn
             |> assert_entries
             |> List.map ~f:snd
             |> List.fold_map ~init:(env'',s)
               ~f:(fun (a,b) c -> (set_of_matches a b c.matches ws, c.action) |> f)
    end in
  let actions = List.filter props' ~f:is_actionref
                |> List.hd_exn
                |> assert_actionref in
  let default = List.filter props' ~f:is_default
                |> default_of_defaults in
  let (final_entries, ks') = if mks = ["lpm"] then (sort_lpm entries, ks)
    else if sort_mks then filter_lpm_prod mks ks entries
    else (entries, ks) in
  let v = VTable { name = name;
                   keys = ks';
                   actions = actions;
                   default_action = default;
                   const_entries = final_entries; } in
  EvalEnv.insert_val name v env'''

and filter_lpm_prod (mks : string list) (ks : value list)
    (entries : (set * Table.action_ref) list)
  : (set * Table.action_ref) list * (value list) =
  let index = match List.findi mks ~f:(fun _ s -> s = "lpm") with
    | None -> failwith "unreachable, should have lpm"
    | Some (i,_) -> i in
  let entries = List.filter entries ~f:(fun (s,a) -> values_match_set ks s)
                |> List.map ~f:(fun (s,a) -> match s with
                    | SProd l -> (List.nth_exn l index, a)
                    | _ -> failwith "not lpm prod") in
  let ks' = [List.nth_exn ks index] in
  (sort_lpm entries, ks')

and check_lpm (mks : string list) : bool =
  let num_lpm = mks
                |> List.filter ~f:(fun s -> s = "lpm")
                |> List.length in
  if num_lpm > 1 then failwith "more than one lpm" else num_lpm = 1

and sort_lpm (entries : (set * Table.action_ref) list)
  : (set * Table.action_ref) list =
  let entries' = List.map entries ~f:(fun (x,y) -> lpm_set_of_set x, y) in
  let (entries'', uni) =
    begin
      match List.findi entries' ~f:(fun i (s,_) -> s = SUniversal) with
      | None -> (entries', None)
      | Some (i,_) -> let es = List.filteri entries' ~f:(fun ind _ -> ind < i) in
        let u = List.nth_exn entries' i in
        (es, Some u)
    end in
  let compare = fun (s1,_) (s2,_) ->
    let (_,n1,_) = assert_lpm s1 in
    let (_,n2,_) = assert_lpm s2 in
    if Bigint.(n1 = n2) then 0
    else if Bigint.(n1 > n2) then -1
    else 1 in
  let sorted = List.sort entries'' ~compare:compare in
  match uni with
  | None -> sorted
  | Some u -> sorted @ [u]

and assert_lpm (s : set) : value * Bigint.t * value =
  match s with
  | SLpm (v1,bs,v2) -> (v1,bs,v2)
  | SUniversal -> failwith "universal"
  | _ -> failwith "not lpm"

and lpm_set_of_set (s : set) : set =
  match s with
  | SSingleton (w,v) ->
    SLpm (VBit (w,v), w, VBit(w,bitwise_neg_of_bigint Bigint.zero w))
  | SUniversal -> SUniversal
  | SMask (v1,v2) ->
    SLpm (v1, v2 |> bigint_of_val |> bits_of_lpmmask Bigint.zero false, v2)
  | SRange _ -> failwith "unreachable"
  | SProd l -> List.map l ~f:lpm_set_of_set |> SProd
  | v -> v

and bits_of_lpmmask (acc : Bigint.t) (b : bool) (v : Bigint.t) : Bigint.t =
  let two = Bigint.(one + one) in
  if Bigint.(v = zero)
  then acc
  else if Bigint.(v % two = zero)
  then if b then failwith "bad lpm mask"
       else bits_of_lpmmask acc b Bigint.(v / two)
  else bits_of_lpmmask Bigint.(acc + one) true Bigint.(v/two)

and is_default (p : Table.pre_property) : bool =
  match p with
  | Custom {name=(_,"default_action");_} -> true
  | _ -> false

and default_of_defaults
    (p : Table.pre_property list) : Table.action_ref =
  let pre = match p with
            | [] ->
              Table.{ annotations = [];
                      name = (Info.dummy,"NoAction");
                      args = [] }
            | (Custom {value;_}) :: _ ->
              let (s,args) = assert_functioncall value in
              Table.{ annotations = [];
                      name = (Info.dummy,s);
                      args = args }
            | _ -> failwith "unreachable" in
  (Info.dummy,pre)

and assert_functioncall (e : Expression.t) : string * Argument.t list =
  match snd e with
  | FunctionCall {func;args;_} ->
    let f' = func |> assert_ename in (f',args)
  | _ -> failwith "expression not a function call"

and assert_ename (e : Expression.t) : string =
  match snd e with
  | Name (_,n) -> n
  | _ -> failwith "expression not a string"

and is_actionref (p : Table.pre_property) : bool =
  match p with
  | Actions _ -> true
  | _ -> false

and assert_actionref (p : Table.pre_property) : Table.action_ref list =
  match p with
  | Actions{actions} -> actions
  | _ -> failwith "not an action ref list"

and is_entries (p : Table.pre_property) : bool =
  match p with
  | Entries _ -> true
  | _ -> false

and assert_entries (p : Table.pre_property) : Table.entry list =
  match p with
  | Entries{entries=es} -> es
  | _ -> failwith "not an entries"

and is_key (p : Table.pre_property) : bool =
  match p with
  | Key _ -> true
  | _ -> false

and assert_key (p : Table.pre_property) : Table.key list =
  match p with
  | Key{keys=ks} -> ks
  | _ -> failwith "not a key"

and eval_header_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_union_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_struct_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_error_decl (env : EvalEnv.t) (errs : P4String.t list) : EvalEnv.t =
  let errs' = List.map errs ~f:snd in
  EvalEnv.insert_errs errs' env

and eval_matchkind_decl (env : EvalEnv.t) (mems : P4String.t list) : EvalEnv.t =
  mems
  |> List.map ~f:snd
  |> List.map ~f:(fun a -> (a, VMatchKind))
  |> (fun a -> EvalEnv.insert_vals a env)

and eval_enum_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_senum_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) :EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_extern_obj (env : EvalEnv.t) (name : string)
    (methods : MethodPrototype.t list) (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_val name (VExternObject (name, methods)) env
  |> EvalEnv.insert_decl name decl

and eval_type_def (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_type_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_ctrltyp_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_prsrtyp_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

and eval_pkgtyp_decl (env : EvalEnv.t) (name : string)
    (decl : Declaration.t) : EvalEnv.t =
  EvalEnv.insert_decl name decl env

(*----------------------------------------------------------------------------*)
(* Functions to Calculate Initialization Values *)
(*----------------------------------------------------------------------------*)

and init_val_of_typ (env : EvalEnv.t) (name : string) (typ : Type.t) : value =
  match snd typ with
  | Bool                      -> VBool false
  | Error                     -> VError "NoError"
  | IntType expr              -> init_val_of_int env expr
  | BitType expr              -> init_val_of_bit env expr
  | VarBit expr               -> init_val_of_varbit env expr
  | TopLevelType (_,n)        -> init_val_of_typname env n name true
  | TypeName (_,n)            -> init_val_of_typname env n name false
  | SpecializedType _         -> failwith "specialized init unimplemented"
  | HeaderStack{header; size} -> init_val_of_stack env name header size
  | Tuple l                   -> init_val_of_tuple env typ l
  | Void                      -> VNull
  | DontCare                  -> VNull

and init_val_of_int (env : EvalEnv.t) (expr : Expression.t) : value =
  match thrd3 (eval_expression' env SContinue expr) with
  | VInteger n
  | VBit(_,n)
  | VInt(_,n) -> VInt(n, Bigint.zero)
  | _ -> failwith "int width is not an int"

and init_val_of_bit (env : EvalEnv.t) (expr : Expression.t) : value =
  match thrd3 (eval_expression' env SContinue expr) with
  | VInteger n
  | VBit(_,n)
  | VInt(_,n) -> VBit(n, Bigint.zero)
  | _ -> failwith "bit width is not an int"

and thrd3 (a,b,c) = c

and init_val_of_varbit (env : EvalEnv.t) (expr: Expression.t) : value =
  match thrd3 (eval_expression' env SContinue expr) with
  | VInteger n
  | VBit(_,n)
  | VInt(_,n) -> VVarbit(n, Bigint.zero, Bigint.zero)
  | _ -> failwith "varbit width is not an int"

and init_val_of_typname (env : EvalEnv.t) (tname : string) (vname : string) (b : bool) : value =
  let f = EvalEnv.(if b then find_decl_toplevel else find_decl) in
  match snd (f tname env) with
  | Struct {fields=fs;_}      -> init_val_of_struct env vname fs
  | Header {fields=fs;_}      -> init_val_of_header env vname fs
  | HeaderUnion {fields=fs;_} -> init_val_of_union env vname fs
  | _ -> failwith "decl init value unimplemented"

and init_val_of_stack (env: EvalEnv.t) (name : string)
    (hdr : Type.t) (size : Expression.t) : value =
  let size' = size |> eval_expression' env SContinue |> thrd3 |> bigint_of_val in
  let hdrs = size' |> Bigint.to_int_exn |> List.init ~f:string_of_int
             |> List.map ~f:(fun s -> init_val_of_typ env s hdr) in
  VStack(name, hdrs, size', Bigint.zero)

and init_val_of_tuple (env : EvalEnv.t) (t : Type.t) (l : Type.t list) : value =
  VTuple (List.map l ~f:(init_val_of_typ env ""))

and init_val_of_struct (env : EvalEnv.t) (name : string)
    (fs : Declaration.field list) : value =
  VStruct (name, List.map fs ~f:(init_binding_of_field env))

and init_val_of_header (env : EvalEnv.t) (name : string)
    (fs : Declaration.field list) : value =
  VHeader (name, List.map fs ~f:(init_binding_of_field env), false)

and init_val_of_union (env : EvalEnv.t) (name : string)
    (fs : Declaration.field list) : value =
  let fs' = List.map fs ~f:(init_binding_of_field env) in
  let bs = List.map fs' ~f:(fun (a,b) -> (a,false)) in
  let v = fs' |> List.hd_exn |> snd in
  VUnion (name, v, bs)

(*----------------------------------------------------------------------------*)
(* Statement Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_statement (env :EvalEnv.t) (sign : signal)
    (stm : Statement.t) : (EvalEnv.t * signal) =
  match snd stm with
  | MethodCall{func;type_args=ts;args} -> eval_method_call env sign func args ts
  | Assignment{lhs;rhs}                -> eval_assign env sign lhs rhs
  | DirectApplication{typ;args}        -> eval_app' env sign args typ
  | Conditional{cond;tru;fls}          -> eval_cond env sign cond tru fls
  | BlockStatement{block}              -> eval_block env sign block
  | Exit                               -> eval_exit env sign
  | EmptyStatement                     -> (env, sign)
  | Return{expr}                       -> eval_return env sign expr
  | Switch{expr;cases}                 -> eval_switch env sign expr cases
  | DeclarationStatement{decl}         -> eval_decl_stm env sign decl

and eval_method_call (env : EvalEnv.t) (sign : signal) (func : Expression.t)
    (args : Argument.t list) (ts : Type.t list) : EvalEnv.t * signal =
  match sign with
  | SContinue -> let (e,s,_) = eval_funcall env func args ts in (e,s)
  | SReject
  | SReturn _
  | SExit     -> (env, sign)

and eval_assign (env : EvalEnv.t) (s : signal) (lhs : Expression.t)
    (rhs : Expression.t) : EvalEnv.t * signal =
  match s with
  | SContinue ->
    let (env', s', v) = eval_expression' env SContinue rhs in
    let lv = lvalue_of_expr lhs in
    begin match s' with
      | SReject -> (env', SReject)
      | SContinue -> eval_assign' env' lv v
      | _ -> failwith "unreachable" end
  | SReject
  | SReturn _
  | SExit     -> (env, s)

and eval_app (env : EvalEnv.t) (s : signal) (v : value)
  (args : Argument.t list) : EvalEnv.t * signal * value =
  match s with
  | SContinue ->
    begin match v with
      | VParser {pvs;pparams;plocals;states} ->
        let (env, s) = eval_parser env pparams args pvs plocals states in
        (env,s,VNull)
      | VControl {cvs;cparams;clocals;apply} ->
        let (env,s) = eval_control env cparams args cvs clocals apply in
        (env,s,VNull)
      | VTable {keys;const_entries;name;actions;default_action} ->
        eval_table env keys const_entries name actions default_action
      | _ -> failwith "apply not implemented on type" end
  | SReject
  | SReturn _
  | SExit -> (env, s, VNull)

and eval_table (env : EvalEnv.t) (key : value list)
    (entries : (set * Table.action_ref) list)
    (name : string) (actions : Table.action_ref list)
    (default : Table.action_ref) : EvalEnv.t * signal * value =
  let l = List.filter entries ~f:(fun (s,a) -> values_match_set key s) in
  let action = match l with
               | [] -> default
               | _ -> List.hd_exn l |> snd in
  let action_name = Table.((snd action).name |> snd) in
  let actionv = EvalEnv.find_val action_name env in
  let args = Table.((snd action).args) in
  match actionv with
  | VAction(params,body) ->
    let (env',s,_) = eval_funcall' env params args body in
    let v = VStruct ("", [
                          ("hit", VBool (not (List.is_empty l)));
                          ("action_run", VEnumField (name, action_name))
                         ]) in
    (env',s,v)
  | _ -> failwith "table expects an action"

  (* TODO: double check about scoping - actions before tables? *)

and eval_app' (env : EvalEnv.t) (s : signal) (args : Argument.t list)
(t : Type.t) : EvalEnv.t * signal =
  let (env', sign', v) = eval_nameless env t [] in
  let (env'', sign'',_) = eval_app env' sign' v args in
  (env'',sign'')

and eval_cond (env : EvalEnv.t) (sign : signal) (cond : Expression.t)
    (tru : Statement.t) (fls : Statement.t option) : EvalEnv.t * signal =
  let eval_cond' env cond tru fls =
    let (env', s', v) = eval_expression' env SContinue cond in
    match s' with
    | SReject -> (env',s')
    | SContinue ->
      begin match v with
        | VBool true  -> eval_statement env' SContinue tru
        | VBool false ->
          begin match fls with
            | None -> (env, SContinue)
            | Some fls' -> eval_statement env' SContinue fls'  end
        | _ -> failwith "conditional guard must be a bool" end
    | _ -> failwith "unreachable" in
  match sign with
  | SContinue -> eval_cond' env cond tru fls
  | SReject
  | SReturn _
  | SExit     -> (env, sign)

and eval_block (env : EvalEnv.t) (sign :signal) (block : Block.t) : (EvalEnv.t * signal) =
  let block = snd block in
  let f (env,sign) stm =
    match sign with
    | SContinue -> eval_statement env sign stm
    | SReject
    | SReturn _
    | SExit     -> (env, sign) in
  List.fold_left block.statements ~init:(env,sign) ~f:f

and eval_exit (env : EvalEnv.t) (sign : signal) : (EvalEnv.t * signal) =
  (env, SExit)

and eval_return (env : EvalEnv.t) (sign : signal)
    (expr : Expression.t option) : (EvalEnv.t * signal) =
  let (env',s',v) =
    match expr with
    | None   -> (env, SContinue, VNull)
    | Some e -> eval_expression' env SContinue e in
  match sign with
  | SReject 
  | SReturn _
  | SExit -> (env,sign)
  | SContinue -> begin match s' with
      | SContinue -> (env', SReturn v)
      | SReject   -> (env', SReject)
      | SReturn _
      | SExit     -> failwith "unreachable" end

and assert_enum (v : value) : string = 
  match v with 
  | VEnumField(_,s) -> s 
  | _ -> failwith "not an enum"

and label_matches_string (s : string) (case : Statement.pre_switch_case) : bool =
  match case with 
  | Action{label;_} 
  | FallThrough{label} -> 
    begin match snd label with 
      | Default -> true 
      | Name(_,n) -> s = n end

and eval_switch (env : EvalEnv.t) (sign : signal) (expr : Expression.t)
    (cases : Statement.switch_case list) : EvalEnv.t * signal = 
  let open Statement in 
  let (env',s',v) = eval_expression' env SContinue expr in 
  match sign with 
  | SReject
  | SReturn _ 
  | SExit -> (env, sign)
  | SContinue -> begin match s' with 
    | SReject -> (env', SReject) 
    | SContinue -> 
      let s = assert_enum v in 
      cases 
      |> List.map ~f:snd
      |> List.group ~break:(fun x _ -> match x with Action _ -> true | _ -> false)
      |> List.filter ~f:(fun l -> List.exists l ~f:(label_matches_string s))
      |> List.hd_exn
      |> List.filter ~f:(function Action _ -> true | _ -> false) 
      |> List.hd_exn 
      |> (function Action{label;code} -> code | _ -> failwith "unreachable")
      |> eval_block env' SContinue
    | _ -> failwith "unreachable" end

and eval_decl_stm (env : EvalEnv.t) (sign : signal)
    (decl : Declaration.t) : EvalEnv.t * signal =
  match sign with
  | SContinue -> (eval_decl env decl, SContinue)
  | SReject
  | SReturn _
  | SExit     -> (env, sign)

(*----------------------------------------------------------------------------*)
(* Asssignment Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_assign' (env : EvalEnv.t) (lhs : lvalue)
    (rhs : value) : EvalEnv.t * signal =
  match lhs with
  | LName n            -> (assign_name env n lhs rhs EvalEnv.insert_val, SContinue)
  | LTopName n         -> (assign_name env n lhs rhs EvalEnv.insert_val_toplevel, SContinue)
  | LMember(lv,mname)  -> assign_member env lv mname rhs
  | LBitAccess(lv,m,l) -> assign_bitaccess env lv m l rhs
  | LArrayAccess(lv,e) -> assign_arrayaccess env lv e rhs

and assign_name (env : EvalEnv.t) (name : string) (lhs : lvalue) (rhs : value)
    (f : string -> value -> EvalEnv.t -> EvalEnv.t) : EvalEnv.t =
  let t = EvalEnv.find_typ name env in
  match rhs with
  | VTuple l        -> f name (implicit_cast_from_tuple env lhs name rhs t) env
  | VStruct(n,l)    -> f name (VStruct(name,l)) env
  | VHeader(n,l,b)  -> f name (VHeader(name,l,b)) env
  | VUnion(n,v,l)   -> f name (VUnion(name,v,l)) env
  | VStack(n,v,a,i) -> f name (VStack(name,v,a,i)) env
  | VInteger n      -> f name (implicit_cast_from_rawint env rhs t) env
  | _ -> f name rhs env

and assign_member (env : EvalEnv.t) (lv : lvalue) (mname : string)
    (rhs : value) : EvalEnv.t * signal =
  let (s,v) = value_of_lvalue env lv in
  match s with
  | SContinue ->
    begin match v with
      | VStruct(n,l)       -> assign_struct_mem env lv rhs mname n l
      | VHeader(n,l,b)     -> assign_header_mem env lv rhs mname n l b
      | VUnion(n,vs,bs)    -> assign_union_mem env lv rhs mname n bs
      | VStack(n,hdrs,s,i) -> assign_stack_mem env lv rhs n mname hdrs s i
      | _ -> failwith "member access undefined" end
  | SReject -> (EvalEnv.set_error "StackOutOfBounds" env, s)
  | _ -> failwith "unreachable"

and assign_bitaccess (env : EvalEnv.t) (lv : lvalue) (msb : Expression.t)
    (lsb : Expression.t) (rhs : value) : EvalEnv.t * signal =
  let (env', s, msb') = eval_expression' env SContinue msb in
  let (env'', s', lsb') = eval_expression' env' SContinue lsb in
  match (s,s') with
  | SContinue, SContinue ->
    let lsb'' = bigint_of_val lsb' in
    let msb'' = bigint_of_val msb' in
    let w = Bigint.(msb'' - lsb'' + one) in
    let (s,v) = value_of_lvalue env lv in
    begin match s with
      | SContinue ->
        let n = bigint_of_val v in
        let rhs' = bit_of_rawint (bigint_of_val rhs) w |> bigint_of_val in
        let n0 = bitstring_slice n msb'' lsb'' in
        let diff = Bigint.(n0 - rhs') in
        let diff' = Bigint.(diff * (power_of_two lsb'')) in
        let final = Bigint.(n - diff') in
        eval_assign' env'' lv (VBit(w,final))
      | SReject -> (env'',s)
      | _ -> failwith "unreachable" end
  | SReject, _ -> (env',s)
  | _, SReject -> (env'',s')
  | _ -> failwith "unreachable"

and assign_arrayaccess (env : EvalEnv.t) (lv : lvalue) (e : Expression.t)
    (rhs : value) : EvalEnv.t * signal =
  let (s,v) = value_of_lvalue env lv in
  let (env', s', i) = eval_expression' env SContinue e in
  let i' = bigint_of_val i in
  let t = match snd (typ_of_lvalue env lv) with
    | HeaderStack{header;_} -> header
    | _ -> failwith "not a stack" in
  let rhs' = implicit_cast_from_tuple env (LArrayAccess(lv,e)) (string_of_int (Bigint.to_int_exn i')) rhs t in
  match s,s' with
  | SContinue,SContinue ->
    begin match v with
      | VStack(n,hdrs,size,next) ->
        let (hdrs1, hdrs2) = List.split_n hdrs Bigint.(to_int_exn i') in
        begin match hdrs2 with
          | _ :: t ->
            let hdrs' = hdrs1 @ (rhs' :: t) in
            let rhs'' = VStack(n,hdrs',size,next) in
            eval_assign' env' lv rhs''
          | [] -> (EvalEnv.set_error "StackOutOfBounds" env', SReject) end
      | _ -> failwith "array access is not a header stack" end
  | SReject,_ -> (EvalEnv.set_error "StackOutOfBounds" env, s)
  | _,SReject -> (env', s)
  | _ -> failwith "unreachable"


and assign_struct_mem (env : EvalEnv.t) (lhs : lvalue) (rhs : value)
    (fname : string) (sname : string)
    (l : (string * value) list) : EvalEnv.t * signal =
  let t = typ_of_struct_field env (typ_of_lvalue env lhs) fname in
  let rhs' = implicit_cast_from_rawint env rhs t in
  let rhs'' = implicit_cast_from_tuple env (LMember(lhs, fname)) fname rhs' t in
  eval_assign' env lhs ((VStruct(sname, (fname, rhs'') :: l)))

and assign_header_mem (env : EvalEnv.t) (lhs : lvalue) (rhs : value)
    (fname : string) (hname : string) (l : (string * value) list)
    (b : bool) : EvalEnv.t * signal =
  let t = typ_of_header_field env (typ_of_lvalue env lhs) fname in
  let rhs' = implicit_cast_from_rawint env rhs t in
  eval_assign' env lhs ((VHeader(hname,(fname,rhs') :: l,b)))

and assign_union_mem (env : EvalEnv.t) (lhs : lvalue) (rhs : value)
    (fname : string) (uname : string)
    (vbs : (string * bool) list) : EvalEnv.t * signal =
  let t = typ_of_union_field env (typ_of_lvalue env lhs) fname in
  let rhs' = implicit_cast_from_tuple env (LMember(lhs,fname)) fname rhs t in
  let vbs' = List.map vbs ~f:(fun (s,_) -> (s, s=fname)) in
  eval_assign' env lhs (VUnion(uname, rhs', vbs'))

and assign_stack_mem (env : EvalEnv.t) (lhs : lvalue) (rhs : value)
    (sname : string) (mname : string) (hdrs : value list) (size : Bigint.t)
    (next : Bigint.t) : EvalEnv.t * signal =
  let () =
    match mname with
    | "next" -> ()
    | _ -> failwith "stack mem not an lvalue" in
  if next >= size
  then (env, SReject)
  else
    let t = typ_of_stack_mem env lhs in
    let rhs' = implicit_cast_from_tuple env (LMember(lhs,mname)) mname rhs t in
    let (hdrs1, hdrs2) = List.split_n hdrs Bigint.(to_int_exn next) in
    let hdrs' =
      match hdrs2 with
      | _ :: t -> hdrs1 @ (rhs' :: t)
      | [] -> failwith "header stack is empty" in
    eval_assign' env lhs (VStack(sname,hdrs',size,next))

(*----------------------------------------------------------------------------*)
(* Functions on L-Values*)
(*----------------------------------------------------------------------------*)

and lvalue_of_expr (expr : Expression.t) =
  match snd expr with
  | Name(_,n) -> LName n
  | TopLevel(_,n) -> LTopName n
  | ExpressionMember{expr=e; name=(_,n)} -> LMember(lvalue_of_expr e, n)
  | BitStringAccess{bits;lo;hi} -> LBitAccess(lvalue_of_expr bits, lo, hi)
  | ArrayAccess{array;index} -> LArrayAccess(lvalue_of_expr array, index)
  | _ -> failwith "not an lvalue"

and value_of_lvalue (env : EvalEnv.t) (lv : lvalue) : signal * value =
  match lv with
  | LName n                -> (SContinue, EvalEnv.find_val n env)
  | LTopName n             -> (SContinue, EvalEnv.find_val_toplevel n env)
  | LMember(lv, n)         -> value_of_lmember env lv n
  | LBitAccess(lv, hi, lo) -> value_of_lbit env lv hi lo
  | LArrayAccess(lv, idx)  -> value_of_larray env lv idx

and value_of_lmember (env : EvalEnv.t) (lv : lvalue)
    (n : string) : signal * value =
  let (s,v) = value_of_lvalue env lv in
  let v' = match v with
    | VStruct(_,l)
    | VHeader(_,l, _)  -> List.Assoc.find_exn l n ~equal:(=)
    | VUnion(_,v,_)    -> v
    | VStack(_,vs,s,i) -> value_of_stack_mem_lvalue n vs s i
    | _ -> failwith "no lvalue member" in
  match s with
  | SContinue -> (s,v')
  | SReject -> (s,VNull)
  | _ -> failwith "unreachable"

and value_of_lbit (env : EvalEnv.t) (lv : lvalue) (hi : Expression.t)
    (lo : Expression.t) : signal * value =
  let (_,_,m) = eval_expression' env SContinue hi in
  let (_,_,l) = eval_expression' env SContinue lo in
  let (s,n) = value_of_lvalue env lv in
  let n' = bigint_of_val n in
  let m' = bigint_of_val m in
  let l' = bigint_of_val l in
  match s with
  | SContinue -> (s, VBit(Bigint.(m' - l' + one), bitstring_slice n' m' l'))
  | SReject -> (s, VNull)
  | _ -> failwith "unreachable"

and value_of_larray (env : EvalEnv.t) (lv : lvalue)
    (idx : Expression.t) : signal * value =
  let (s,v) =  value_of_lvalue env lv in
  match s with
  | SContinue ->
    begin match v with
      | VStack(n,vs,s,i) ->
        let idx' = eval_expression' env SContinue idx |> thrd3 |> bigint_of_val in
        begin try (SContinue, List.nth_exn vs Bigint.(to_int_exn (idx' % s)))
          with Invalid_argument _ -> (SReject, VNull) end
      | _ -> failwith "array access is not a header stack" end
  | SReject -> (s,VNull)
  | _ -> failwith "unreachable"

and value_of_stack_mem_lvalue (name : string) (vs : value list)
    (size : Bigint.t) (next : Bigint.t) : value =
  match name with
  | "next" -> List.nth_exn vs Bigint.(to_int_exn (next % size))
  | _ -> failwith "not an lvalue"

and typ_of_lvalue (env : EvalEnv.t) (lv : lvalue) : Type.t =
  match lv with
  | LName s -> EvalEnv.find_typ s env
  | LTopName s -> EvalEnv.find_typ_toplevel s env
  | LMember(lv', s) -> typ_of_lmember env lv' s
  | LBitAccess(lv', e1, e2) -> typ_of_lbit env lv' e1 e2
  | LArrayAccess(lv', e) -> typ_of_larray env lv' e

and typ_of_lmember (env : EvalEnv.t) (lv : lvalue) (s : string) : Type.t =
  let t = typ_of_lvalue env lv in
  match snd t with
  | HeaderStack{header;_} -> typ_of_stack_lmem env s header
  | TypeName(_,n) ->
    begin match snd (decl_of_typ env t) with
      | Header{fields=fs;_}      -> typ_of_struct_lmem env s fs
      | HeaderUnion{fields=fs;_} -> typ_of_struct_lmem env s fs
      | Struct{fields=fs;_}      -> typ_of_struct_lmem env s fs
      | _ -> failwith "lvalue type name member access not defined" end
  | _ -> failwith "type of lvalue member unimplemented"

and typ_of_struct_lmem (env : EvalEnv.t) (s : string)
    (fields : Declaration.field list) : Type.t =
  let fs = List.map fields ~f:(fun a -> (snd (snd a).name, a)) in
  let f = List.Assoc.find_exn fs ~equal:(=) s in
  (snd f).typ

and typ_of_stack_lmem (env : EvalEnv.t) (s : string) (t : Type.t) : Type.t =
  let () =
    match s with
    | "next" -> ()
    | _ -> failwith "stack member not a lvalue" in
  t

and typ_of_lbit (env : EvalEnv.t) (lv : lvalue) (e1 : Expression.t)
    (e2 : Expression.t) : Type.t =
  let (_,_,v1) = eval_expression' env SContinue e1 in
  let (_,_,v2) = eval_expression' env SContinue e2 in
  let n1 = bigint_of_val v1 in
  let n2 = bigint_of_val v2 in
  let n0 = Bigint.(n1 - n2 + one) in
  (Info.dummy, Type.BitType(Info.dummy, Expression.Int(Info.dummy,{value=n0;width_signed=None})))

and typ_of_larray (env : EvalEnv.t) (lv : lvalue) (e : Expression.t) : Type.t =
  let t = typ_of_lvalue env lv in
  match snd t with
  | HeaderStack{header;_} -> header
  | _ -> failwith "array access on non-header stack"

(*----------------------------------------------------------------------------*)
(* Expression Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_expression' (env : EvalEnv.t) (s : signal)
    (exp : Expression.t) : EvalEnv.t * signal * value =
  match s with
  | SContinue ->
    begin match snd exp with
      | True                                 -> (env, s, VBool true)
      | False                                -> (env, s, VBool false)
      | Int(_,n)                             -> (env, s, eval_p4int n)
      | String (_,value)                     -> (env, s, VString value)
      | Name (_,name)                        -> eval_name env s name exp
      | TopLevel (_,name)                    -> (env, s, EvalEnv.find_val_toplevel name env)
      | ArrayAccess{array=a; index=i}        -> eval_array_access env a i
      | BitStringAccess({bits;lo;hi})        -> eval_bitstring_access env bits lo hi
      | List{values}                         -> eval_list env values
      | UnaryOp{op;arg}                      -> eval_unary env op arg
      | BinaryOp{op; args=(l,r)}             -> eval_binop env op l r
      | Cast{typ;expr}                       -> eval_cast env typ expr
      | TypeMember{typ;name}                 -> eval_typ_mem env typ (snd name)
      | ErrorMember t                        -> (env, s, EvalEnv.find_err (snd t) env)
      | ExpressionMember{expr;name}          -> eval_expr_mem env expr name
      | Ternary{cond;tru;fls}                -> eval_ternary env cond tru fls
      | FunctionCall{func;type_args=ts;args} -> eval_funcall env func args ts
      | NamelessInstantiation{typ;args}      -> eval_nameless env typ args
      | Mask{expr;mask}                      -> eval_mask env expr mask
      | Range{lo;hi}                         -> eval_range env lo hi end
  | SReject -> (env, s, VNull)
  | SReturn _ -> failwith "expression should not return"
  | SExit -> failwith "expresion should not exit"

and eval_name (env : EvalEnv.t) (s : signal) (name : string) (exp : Expression.t)
  : EvalEnv.t * signal * value =
  if name = "verify" then (env, s, VBuiltinFun (name, lvalue_of_expr exp))
  else (env, s, EvalEnv.find_val name env)

and eval_p4int (n : P4Int.pre_t) : value =
  match n.width_signed with
  | None          -> VInteger n.value
  | Some(w,true)  -> VInt (Bigint.of_int w, n.value)
  | Some(w,false) -> VBit (Bigint.of_int w, n.value)

and eval_array_access (env : EvalEnv.t) (a : Expression.t)
    (i : Expression.t) : EvalEnv.t * signal * value =
  let (env', s, a') = eval_expression' env SContinue a in
  let (env'', s', i') = eval_expression' env' SContinue i in
  let idx = bigint_of_val i' in
  let (name,hdrs,size,next) = assert_stack a' in
  let idx' = Bigint.(to_int_exn (idx % size)) in
  match (s,s') with
  | SContinue, SContinue -> (env'', SContinue, List.nth_exn hdrs idx')
  | SReject,_ -> (env',s, VNull)
  | _,SReject -> (env'',s',VNull)
  | _ -> failwith "unreachable"

and eval_bitstring_access (env : EvalEnv.t) (b : Expression.t)
    (m : Expression.t) (l : Expression.t) : EvalEnv.t * signal * value =
  let (env', s, m) = eval_expression' env SContinue m in
  let (env'', s', l) = eval_expression' env' SContinue l in
  let (env''', s'', b) = eval_expression' env'' SContinue b in
  let m' = bigint_of_val m in
  let l' = bigint_of_val l in
  let b' = bigint_of_val b in
  let w = Bigint.(m'-l' + one) in
  let n = bitstring_slice b' m' l' in
  match (s,s',s'') with
  | SContinue, SContinue, SContinue -> (env''', SContinue, VBit(w,n))
  | SReject,_,_ -> (env',s,VNull)
  | _,SReject,_ -> (env'', s,VNull)
  | _,_,SReject -> (env''', s, VNull)
  | _ -> failwith "unreachable"

and eval_list (env : EvalEnv.t)
    (values : Expression.t list) : EvalEnv.t * signal * value =
  let f (a,b) c =
    let (x,y,z) = eval_expression' a b c in
    ((x,y),z) in
  values
  |> List.fold_map ~f:f ~init:(env,SContinue)
  |> (fun ((e,s),l) -> (e, s, VTuple l))

and eval_unary (env : EvalEnv.t) (op : Op.uni)
    (e : Expression.t) : EvalEnv.t * signal * value =
  let (env', s, v) = eval_expression' env SContinue e in
  match s with
  | SContinue ->
    let (env,v) = match snd op with
      | Not    -> eval_not env' v
      | BitNot -> eval_bitnot env' v
      | UMinus -> eval_uminus env' v in
    (env,s,v)
  | SReject -> (env',s,VNull)
  | _ -> failwith "unreachable"

and eval_binop (env : EvalEnv.t) (op : Op.bin) (l : Expression.t)
    (r : Expression.t) : EvalEnv.t * signal * value =
  let (env',s,l) = eval_expression' env SContinue l in
  let (env'',s',r) = eval_expression' env' SContinue r in
  let v = match snd op with
    | Plus     -> eval_bplus l r
    | PlusSat  -> eval_bplus_sat l r
    | Minus    -> eval_bminus l r
    | MinusSat -> eval_bminus_sat l r
    | Mul      -> eval_bmult l r
    | Div      -> eval_bdiv l r
    | Mod      -> eval_bmod l r
    | Shl      -> eval_bshl l r
    | Shr      -> eval_bshr l r
    | Le       -> eval_ble l r
    | Ge       -> eval_bge l r
    | Lt       -> eval_blt l r
    | Gt       -> eval_bgt l r
    | Eq       -> eval_beq l r
    | NotEq    -> eval_bne l r
    | BitAnd   -> eval_bitwise_and l r
    | BitXor   -> eval_bitwise_xor l r
    | BitOr    -> eval_bitwise_or l r
    | PlusPlus -> eval_concat l r
    | And      -> eval_band l r
    | Or       -> eval_bor l r in
  match (s,s') with
  | SContinue, SContinue -> (env'', SContinue, v)
  | SReject,_ -> (env',s,VNull)
  | _,SReject -> (env'',s',VNull)
  | _ -> failwith "unreachable"

and eval_cast (env : EvalEnv.t) (typ : Type.t)
    (expr : Expression.t) : EvalEnv.t * signal * value =
  let (env', s, v) = eval_expression' env SContinue expr in
  let (env'',s',v') =
    match snd typ with
    | Bool -> (env', SContinue, bool_of_val v)
    | BitType e -> bit_of_val env' e v
    | IntType e -> int_of_val env' e v
    | TypeName (_,n) -> (env', s, v)
    | _ -> failwith "type cast unimplemented" in
  match (s,s') with
  | SContinue,SContinue -> (env'',s,v')
  | SReject,_ -> (env',s,VNull)
  | _,SReject -> (env'',s',VNull)
  | _ -> failwith "unreachable"

and eval_typ_mem (env : EvalEnv.t) (typ : Type.t)
    (name : string) : EvalEnv.t * signal * value =
  match snd (decl_of_typ env typ) with
  | Declaration.Enum {members=ms;name=(_,n);_} ->
    let mems = List.map ms ~f:snd in
    if List.mem mems name ~equal:(=)
    then (env, SContinue, VEnumField (n, name))
    else raise (UnboundName name)
  | Declaration.SerializableEnum {members=ms;name=(_,n);typ;_ } ->
    let ms' = List.map ms ~f:(fun (a,b) -> (snd a, b)) in
    let expr = List.Assoc.find_exn ms' ~equal:(=) name in
    let (env',s,v) = eval_expression' env SContinue expr in
    let v' = implicit_cast_from_rawint env' v typ in
    begin match s with
      | SContinue -> (env',s,VSenumField(n,name,v'))
      | SReject -> (env',s,VNull)
      | _ -> failwith "unreachable" end
  | _ -> failwith "typ mem undefined"

and eval_expr_mem (env : EvalEnv.t) (expr : Expression.t)
    (name : P4String.t) : EvalEnv.t * signal * value =
  let (env', s, v) = eval_expression' env SContinue expr in
  match s with
  | SContinue ->
    begin match v with
      | VNull
      | VBool _
      | VInteger _
      | VBit _
      | VInt _
      | VVarbit _
      | VTuple _
      | VSet _
      | VString _
      | VError _
      | VMatchKind
      | VFun _
      | VBuiltinFun _
      | VAction _
      | VEnumField _
      | VSenumField _
      | VExternFun _
      | VPackage _          -> failwith "expr member does not exist"
      | VStruct (_,fs)      -> eval_struct_mem env' (snd name) fs
      | VHeader (_,fs,vbit) -> eval_header_mem env' (snd name) expr fs vbit
      | VUnion (_,v,_)      -> (env', SContinue, v)
      | VStack (_,hdrs,s,n) -> eval_stack_mem env' (snd name) expr hdrs s n
      | VRuntime v          -> eval_runtime_mem env' (snd name) expr v
      | VExternObject _     -> failwith "expr member unimplemented"
      | VParser _
      | VControl _          -> (env', s, VBuiltinFun (snd name, lvalue_of_expr expr))
      | VTable _            -> (env', s, VBuiltinFun (snd name, lvalue_of_expr expr)) end
  | SReject -> (env',s,VNull)
  | _ -> failwith "unreachable"

and eval_ternary (env : EvalEnv.t) (c : Expression.t)
    (te : Expression.t) (fe : Expression.t) : EvalEnv.t * signal * value =
  let (env', s, c') = eval_expression' env SContinue c in
  match c' with
  | VBool(true)  -> (eval_expression' env' s te)
  | VBool(false) -> (eval_expression' env' s fe)
  | _ -> failwith "ternary guard must be a bool"

and eval_funcall (env : EvalEnv.t) (func : Expression.t)
    (args : Argument.t list) (ts : Type.t list) : EvalEnv.t * signal * value =
  let (env', s, cl) = eval_expression' env SContinue func in
  match s with
  | SContinue ->
    begin match cl with
      | VAction (params, body)
      | VFun (params, body)    -> eval_funcall' env' params args body
      | VBuiltinFun(n,lv)      -> eval_builtin env n lv args ts
      | _ -> failwith "unreachable" end
  | SReject -> (env',s,VNull)
  | _ -> failwith "unreachable"

and eval_nameless (env : EvalEnv.t) (typ : Type.t)
    (args : Argument.t list) : EvalEnv.t * signal * value =
  let (info ,decl) = decl_of_typ env typ in
  let (env',s,v) = match decl with
    | Control typ_decl ->
      let (env',s) = copyin env typ_decl.constructor_params args in
      let state = env' |> EvalEnv.get_val_firstlevel |> List.rev in
      let v' = VControl { cvs = state;
                          cparams = typ_decl.params;
                          clocals = typ_decl.locals;
                          apply = typ_decl.apply; } in
      (EvalEnv.pop_scope env',s,v')
    | Parser typ_decl ->
      let (env',s) = copyin env typ_decl.constructor_params args in
      let state = env' |> EvalEnv.get_val_firstlevel |> List.rev in
      let v' = VParser { pvs = state;
                         pparams = typ_decl.params;
                         plocals = typ_decl.locals;
                         states = typ_decl.states; } in
      (EvalEnv.pop_scope env',s,v')
    | PackageType pack_decl ->
      let (env',s) = copyin env pack_decl.params args in
      let state = env' |> EvalEnv.get_val_firstlevel |> List.rev in
      (EvalEnv.pop_scope env', s, VPackage((info, decl), state))
    | _ -> failwith "instantiation unimplemented" in
  match s with
  | SContinue -> (env',s,v)
  | SReject -> (env,s,VNull)
  | _ -> failwith "nameless should not return or exit"

and eval_mask (env : EvalEnv.t) (e : Expression.t)
    (m : Expression.t) : EvalEnv.t * signal * value =
  let (env', s, v1)  = eval_expression' env SContinue e in
  let (env'', s', v2) = eval_expression' env' SContinue m in
  match (s,s') with
  | SContinue, SContinue -> (env'', s, VSet(SMask(v1,v2)))
  | SReject,_ -> (env',s,VNull)
  | _,SReject -> (env'',s',VNull)
  | _ -> failwith "unreachable"

and eval_range (env : EvalEnv.t) (lo : Expression.t)
    (hi : Expression.t) : EvalEnv.t * signal * value =
  let (env', s, v1)  = eval_expression' env SContinue lo in
  let (env'', s', v2) = eval_expression' env' SContinue hi in
  match (s,s') with
  | SContinue, SContinue -> (env'', s, VSet(SRange(v1,v2)))
  | SReject,_ -> (env',s,VNull)
  | _,SReject -> (env'',s',VNull)
  | _ -> failwith "unreachable"

(*----------------------------------------------------------------------------*)
(* Unary Operator Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_not (env : EvalEnv.t) (v : value) : EvalEnv.t * value =
  match v with
  | VBool b -> (env, VBool (not b))
  | _ -> failwith "not operator can only be applied to bools"

and eval_bitnot (env : EvalEnv.t) (v : value) : EvalEnv.t * value =
  match v with
  | VBit(w,n) -> (env, VBit(w, bitwise_neg_of_bigint n w))
  | VInt(w,n) -> (env, VBit(w, ((of_twos_complement n w
                                 |> bitwise_neg_of_bigint) w
                                |> to_twos_complement) w))
  | _ -> failwith "bitwise complement on non-fixed width unsigned bitstring"

and bitwise_neg_of_bigint (n : Bigint.t) (w : Bigint.t) : Bigint.t =
  if Bigint.(w > zero) then
    let w' = power_of_two Bigint.(w-one) in
    let g = bitstring_slice n Bigint.(w - one) Bigint.(w - one) in
    if Bigint.(g = zero)
    then bitwise_neg_of_bigint Bigint.(n + w') Bigint.(w-one)
    else bitwise_neg_of_bigint Bigint.(n - w') Bigint.(w-one)
  else n

and eval_uminus (env : EvalEnv.t) (v : value) : EvalEnv.t * value =
  match v with
  | VBit(w,n)  -> Bigint.(env, VBit(w, (power_of_two w) - n))
  | VInt(w,n)  -> Bigint.(env, VInt(w, to_twos_complement (-n) w))
  | VInteger n -> (env, VInteger (Bigint.neg n))
  | _ -> failwith "unary minus on non-int type"

(*----------------------------------------------------------------------------*)
(* Binary Operator Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_bplus (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w,v1), VBit(_,v2)   -> VBit(w, of_twos_complement Bigint.(v1 + v2) w)
  | VInt(w,v1), VInt(_,v2)   -> VInt(w, to_twos_complement Bigint.(v1 + v2) w)
  | VBit(w,v1), VInteger n   -> eval_bplus l (bit_of_rawint n w)
  | VInteger n, VBit(w,v1)   -> eval_bplus (bit_of_rawint n w) r
  | VInt(w,v1), VInteger n   -> eval_bplus l (int_of_rawint n w)
  | VInteger n, VInt(w,v1)   -> eval_bplus (int_of_rawint n w) r
  | VInteger n1, VInteger n2 -> VInteger Bigint.(n1 + n2)
  | _ -> failwith "binary plus operation only defined on ints"

and eval_bplus_sat (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w,v1), VBit(_,v2) -> unsigned_op_sat v1 v2 w Bigint.(+)
  | VInt(w,v1), VInt(_,v2) -> signed_op_sat v1 v2 w Bigint.(+)
  | VBit(w,v1), VInteger n -> eval_bplus_sat l (bit_of_rawint n w)
  | VInteger n, VBit(w,_)  -> eval_bplus_sat (bit_of_rawint n w) r
  | VInt(w,_), VInteger n  -> eval_bplus_sat l (int_of_rawint n w)
  | VInteger n, VInt(w,_)  -> eval_bplus_sat (int_of_rawint n w) r
  | _ -> failwith "binary sat plus operation only definted on fixed-width ints"

and eval_bminus (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w,v1), VBit(_,v2)   -> VBit(w, of_twos_complement Bigint.(v1 - v2) w)
  | VInt(w,v1), VInt(_,v2)   -> VInt(w, to_twos_complement Bigint.(v1 - v2) w)
  | VBit(w,v1), VInteger n   -> eval_bminus l (bit_of_rawint n w)
  | VInteger n, VBit(w,v1)   -> eval_bminus (bit_of_rawint n w) r
  | VInt(w,v1), VInteger n   -> eval_bminus l (int_of_rawint n w)
  | VInteger n, VInt(w,v1)   -> eval_bminus (int_of_rawint n w) r
  | VInteger n1, VInteger n2 -> VInteger Bigint.(n1 - n2)
  | _ -> failwith "binary plus operation only defined on ints"

and eval_bminus_sat (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w,v1), VBit(_,v2) -> unsigned_op_sat v1 v2 w Bigint.(-)
  | VInt(w,v1), VInt(_,v2) -> signed_op_sat v1 v2 w Bigint.(-)
  | VBit(w,v1), VInteger n -> eval_bminus_sat l (bit_of_rawint n w)
  | VInteger n, VBit(w,_)  -> eval_bminus_sat (bit_of_rawint n w) r
  | VInt(w,_), VInteger n  -> eval_bminus_sat l (int_of_rawint n w)
  | VInteger n, VInt(w,_)  -> eval_bminus_sat (int_of_rawint n w) r
  | _ -> failwith "binary sat plus operation only definted on fixed-width ints"

and eval_bmult (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w,v1), VBit(_,v2)   -> VBit(w, of_twos_complement Bigint.(v1 * v2) w)
  | VInt(w,v1), VInt(_,v2)   -> VInt(w, to_twos_complement Bigint.(v1 * v2) w)
  | VBit(w,v1), VInteger n   -> eval_bmult l (bit_of_rawint n w)
  | VInteger n, VBit(w,v1)   -> eval_bmult (bit_of_rawint n w) r
  | VInt(w,v1), VInteger n   -> eval_bmult l (int_of_rawint n w)
  | VInteger n, VInt(w,v1)   -> eval_bmult (int_of_rawint n w) r
  | VInteger n1, VInteger n2 -> VInteger Bigint.(n1 * n2)
  | _ -> failwith "binary mult operation only defined on ints"

and eval_bdiv (l : value) (r : value) : value =
  match (l,r) with
  | VInteger n1, VInteger n2 -> VInteger Bigint.(n1 / n2)
  | _ -> failwith "division only defined on raw ints"

and eval_bmod (l : value) (r : value) : value =
  match (l,r) with
  | VInteger n1, VInteger n2 -> VInteger Bigint.(n1 % n2)
  | _ -> failwith "mod only defined on raw ints"

and eval_bshl (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w,v1), VBit(_,v2)
  | VBit(w,v1), VInteger v2  -> VBit(w, of_twos_complement (shift_bigint_left v1 v2) w)
  | VInt(w,v1), VBit(_,v2)
  | VInt(w,v1), VInteger v2  -> VInt(w, to_twos_complement (shift_bigint_left v1 v2) w)
  | VInteger v1, VInteger v2 -> VInteger(shift_bigint_left v1 v2)
  | _ -> failwith "shift left operator not defined for these types"

and eval_bshr (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w,v1), VBit(_,v2)
  | VBit(w,v1), VInteger v2  -> VBit(w, of_twos_complement (shift_bigint_right v1 v2) w)
  | VInt(w,v1), VBit(_,v2)
  | VInt(w,v1), VInteger v2  -> VInt(w, to_twos_complement (shift_bigint_right v1 v2) w)
  | VInteger v1, VInteger v2 -> VInteger(shift_bigint_right v1 v2)
  | _ -> failwith "shift right operator not defined for these types"

and eval_ble (l : value) (r : value) : value =
  match (l,r) with
  | VBit(_,v1), VBit(_,v2)
  | VInteger v1, VInteger v2
  | VInt(_,v1), VInt(_,v2)  -> VBool Bigint.(v1 <= v2)
  | VInteger v1, VBit(w,v2) -> eval_ble (bit_of_rawint v1 w) r
  | VBit(w,v1), VInteger v2 -> eval_ble l (bit_of_rawint v2 w)
  | VInteger v1, VInt(w,v2) -> eval_ble (int_of_rawint v1 w) r
  | VInt(w,v1), VInteger v2 -> eval_ble l (int_of_rawint v2 w)
  | _ -> failwith "leq operator only defined on int types"

and eval_bge (l : value) (r : value) : value =
  match (l,r) with
  | VBit(_,v1), VBit(_,v2)
  | VInteger v1, VInteger v2
  | VInt(_,v1), VInt(_,v2)  -> VBool Bigint.(v1 >= v2)
  | VInteger v1, VBit(w,v2) -> eval_bge (bit_of_rawint v1 w) r
  | VBit(w,v1), VInteger v2 -> eval_bge l (bit_of_rawint v2 w)
  | VInteger v1, VInt(w,v2) -> eval_bge (int_of_rawint v1 w) r
  | VInt(w,v1), VInteger v2 -> eval_bge l (int_of_rawint v2 w)
  | _ -> failwith "geq operator only defined on int types"

and eval_blt (l : value) (r : value) : value =
  match (l,r) with
  | VBit(_,v1), VBit(_,v2)
  | VInteger v1, VInteger v2
  | VInt(_,v1), VInt(_,v2)  -> VBool Bigint.(v1 < v2)
  | VInteger v1, VBit(w,v2) -> eval_blt (bit_of_rawint v1 w) r
  | VBit(w,v1), VInteger v2 -> eval_blt l (bit_of_rawint v2 w)
  | VInteger v1, VInt(w,v2) -> eval_blt (int_of_rawint v1 w) r
  | VInt(w,v1), VInteger v2 -> eval_blt l (int_of_rawint v2 w)
  | _ -> failwith "lt operator only defined on int types"

and eval_bgt (l : value) (r : value) : value =
  match (l,r) with
  | VBit(_,v1), VBit(_,v2)
  | VInteger v1, VInteger v2
  | VInt(_,v1), VInt(_,v2)  -> VBool Bigint.(v1 > v2)
  | VInteger v1, VBit(w,v2) -> eval_bgt (bit_of_rawint v1 w) r
  | VBit(w,v1), VInteger v2 -> eval_bgt l (bit_of_rawint v2 w)
  | VInteger v1, VInt(w,v2) -> eval_bgt (int_of_rawint v1 w) r
  | VInt(w,v1), VInteger v2 -> eval_bgt l (int_of_rawint v2 w)
  | _ -> failwith "gt operator only defined on int types"

and eval_beq (l : value) (r : value) : value =
  match (l,r) with
  | VError s1, VError s2
  | VEnumField(_,s1), VEnumField(_,s2)       -> VBool(s1 = s2)
  | VSenumField(_,_,v1), VSenumField(_,_,v2) -> eval_beq v1 v2
  | VBool b1, VBool b2                       -> VBool(b1 = b2)
  | VBit(_,n1), VBit(_,n2)
  | VInteger n1, VInteger n2
  | VInt(_,n1), VInt(_,n2)                   -> VBool Bigint.(n1 = n2)
  | VVarbit(_,w1,n1), VVarbit(_,w2, n2)      -> VBool(Bigint.(n1 = n2 && w1 = w2))
  | VBit(w,n1), VInteger n2                  -> eval_beq l (bit_of_rawint n2 w)
  | VInteger n1, VBit(w,n2)                  -> eval_beq (bit_of_rawint n1 w) r
  | VInt(w,n1), VInteger n2                  -> eval_beq l (int_of_rawint n2 w)
  | VInteger n1, VInt(w,n2)                  -> eval_beq (int_of_rawint n1 w) r
  | VStruct(_,l1), VStruct(_,l2)             -> structs_equal l1 l2
  | VHeader(_,l1,b1), VHeader(_,l2,b2)       -> headers_equal l1 l2 b1 b2
  | VStack(_,l1,_,_), VStack(_,l2,_,_)       -> stacks_equal l1 l2
  | VUnion(_,v1,l1), VUnion(_,v2,l2)         -> unions_equal v1 v2 l1 l2
  | VTuple _, _ -> failwith "got tuple"
  | _ -> failwith "equality comparison undefined for given types"

and eval_bne (l : value) (r : value) : value =
  eval_beq l r |> assert_bool |> not |> VBool

and eval_bitwise_and (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w,v1), VBit(_,v2) -> VBit(w, Bigint.bit_and v1 v2)
  | VBit(w,v1), VInteger n -> eval_bitwise_and l (bit_of_rawint n w)
  | VInteger n, VBit(w,v2) -> eval_bitwise_and (bit_of_rawint n w) r
  | VInt(w,v1), VInt(_,v2) -> bitwise_op_of_signeds Bigint.bit_and v1 v2 w
  | VInt(w,v1), VInteger n -> eval_bitwise_and l (bit_of_rawint n w)
  | VInteger n, VInt(w,v2) -> eval_bitwise_and (bit_of_rawint n w) r
  | _ -> failwith "bitwise and only defined on fixed width ints"

and eval_bitwise_xor (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w,v1), VBit(_,v2) -> VBit(w, Bigint.bit_xor v1 v2)
  | VBit(w,v1), VInteger n -> eval_bitwise_xor l (bit_of_rawint n w)
  | VInteger n, VBit(w,v2) -> eval_bitwise_xor (bit_of_rawint n w) r
  | VInt(w,v1), VInt(_,v2) -> bitwise_op_of_signeds Bigint.bit_xor v1 v2 w
  | VInt(w,v1), VInteger n -> eval_bitwise_xor l (bit_of_rawint n w)
  | VInteger n, VInt(w,v2) -> eval_bitwise_xor (bit_of_rawint n w) r
  | _ -> failwith "bitwise xor only defined on fixed width ints"

and eval_bitwise_or (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w,v1), VBit(_,v2) -> VBit(w, Bigint.bit_or v1 v2)
  | VBit(w,v1), VInteger n -> eval_bitwise_or l (bit_of_rawint n w)
  | VInteger n, VBit(w,v2) -> eval_bitwise_or (bit_of_rawint n w) r
  | VInt(w,v1), VInt(_,v2) -> bitwise_op_of_signeds Bigint.bit_or v1 v2 w
  | VInt(w,v1), VInteger n -> eval_bitwise_or l (bit_of_rawint n w)
  | VInteger n, VInt(w,v2) -> eval_bitwise_or (bit_of_rawint n w) r
  | _ -> failwith "bitwise or only defined on fixed width ints"

and eval_concat (l : value) (r : value) : value =
  match (l,r) with
  | VBit(w1,v1), VBit(w2,v2) -> VBit(Bigint.(w1+w2), Bigint.(shift_bigint_left v1 w2 + v2))
  | VBit(w,v), VInteger n    -> eval_concat l (bit_of_rawint n w)
  | VInteger n, VBit(w,v)    -> eval_concat (bit_of_rawint n w) r
  | _ -> failwith "concat operator only defined on unsigned ints"

and eval_band (l : value) (r : value) : value =
  match (l,r) with
  | VBool b1, VBool b2 -> VBool(b1 && b2)
  | _ -> failwith "and operator only defined on bools"

and eval_bor (l : value) (r : value) : value =
  match (l,r) with
  | VBool b1, VBool b2 -> VBool(b1 || b2)
  | _ -> failwith "or operator only defined on bools"

and bigint_max (n : Bigint.t) (m : Bigint.t) : Bigint.t =
  if Bigint.(n>m) then n else m

and bigint_min (n : Bigint.t) (m : Bigint.t) : Bigint.t =
  if Bigint.(n<m) then n else m

and unsigned_op_sat (l : Bigint.t) (r : Bigint.t) (w : Bigint.t)
    (op : Bigint.t -> Bigint.t -> Bigint.t) : value =
  let x = power_of_two w in
  let n = op l r in
  let n' =
    if Bigint.(n > zero)
    then bigint_min n Bigint.(x - one)
    else bigint_max n Bigint.zero in
  VBit(w, n')

and signed_op_sat (l : Bigint.t) (r : Bigint.t) (w : Bigint.t)
    (op : Bigint.t -> Bigint.t -> Bigint.t) : value =
  let x = power_of_two Bigint.(w-one) in
  let n = op l r in
  let n' =
    if Bigint.(n > zero)
    then bigint_min n Bigint.(x - one)
    else bigint_max n Bigint.(-x) in
  VInt(w, n')

and shift_bigint_left (v : Bigint.t) (o : Bigint.t) : Bigint.t =
  if Bigint.(o > zero)
  then shift_bigint_left Bigint.(v * (one + one)) Bigint.(o - one)
  else v

and shift_bigint_right (v : Bigint.t) (o : Bigint.t) : Bigint.t =
  if Bigint.(v = -one)
  then v
  else if Bigint.(o > zero)
  then shift_bigint_right Bigint.(v / (one + one)) Bigint.(o - one)
  else v

and bitwise_op_of_signeds (op : Bigint.t -> Bigint.t -> Bigint.t)
    (v1 : Bigint.t) (v2 : Bigint.t) (w : Bigint.t) : value =
  let v1' = of_twos_complement v1 w in
  let v2' = of_twos_complement v2 w in
  let n = op v1' v2' in
  VBit(w,to_twos_complement n w)

and structs_equal (l1 : (string * value) list)
    (l2 : (string * value) list) : value =
  let f (a : (string * value) list) (b : string * value) =
    if List.Assoc.mem a ~equal:(=) (fst b)
    then a
    else b :: a in
  let l1' = List.fold_left l1 ~init:[] ~f:f in
  let l2' = List.fold_left l2 ~init:[] ~f:f in
  let g (a,b) =
    let h = (fun (x,y) -> x = a && assert_bool (eval_beq y b)) in
    List.exists l2' ~f:h in
  let b = List.for_all l1' ~f:g in
  VBool b

and headers_equal (l1 : (string * value) list) (l2 : (string * value) list)
    (b1 : bool) (b2 : bool) : value =
  let a = (not b1 && not b2) in
  let b = (b1 && b2 && assert_bool (structs_equal l1 l2)) in
  VBool (a || b)

and stacks_equal (l1 : value list) (l2 : value list) : value =
  let f = (fun i a -> a |> eval_beq (List.nth_exn l2 i) |> assert_bool) in
  let b = List.for_alli l1 ~f:f in
  VBool b

and unions_equal (v1 : value) (v2 : value) (l1 : (string * bool) list)
    (l2 : (string * bool) list) : value =
  let f = fun (_,x) -> not x in
  let b1 = (List.for_all l1 ~f:f) && (List.for_all l2 ~f:f) in
  let l1' = List.map l1 ~f:(fun (x,y) -> (y,x)) in
  let l2' = List.map l2 ~f:(fun (x,y) -> (y,x)) in
  let b2 = List.Assoc.find l1' true ~equal:(=) = List.Assoc.find l2' true ~equal:(=) in
  let b3 = eval_beq v1 v2 |> assert_bool in
  VBool (b1 || (b2 && b3))

(*----------------------------------------------------------------------------*)
(* Type Casting Evaluation *)
(*----------------------------------------------------------------------------*)

and bool_of_val (v : value) : value =
  match v with
  | VBit(w,n) when Bigint.(w = one) -> VBool Bigint.(n = one)
  | _ -> failwith "cast to bool undefined"

and bit_of_val (env : EvalEnv.t) (e : Expression.t)
    (v : value) : EvalEnv.t * signal * value =
  let (env', s, x) = eval_expression' env SContinue e in
  let w = bigint_of_val x in
  let v' = match v with
    | VInt(_,n)
    | VBit(_,n)
    | VInteger n -> bit_of_rawint n w
    | _ -> failwith "cast to bitstring undefined" in
  match s with
  | SContinue -> (env', s,v')
  | SReject -> (env',s,VNull)
  | _ -> failwith "unreachable"

and int_of_val (env : EvalEnv.t) (e : Expression.t)
    (v : value) : EvalEnv.t * signal * value =
  let (env', s, x) = eval_expression' env SContinue e in
  let w = bigint_of_val x in
  let v' = match v with
    | VBit(_,n)
    | VInt(_,n)
    | VInteger n -> int_of_rawint n w
    | _ -> failwith "cast to bitstring undefined" in
  match s with
  | SContinue -> (env', s,v')
  | SReject -> (env',s,VNull)
  | _ -> failwith "unreachable"

and bit_of_rawint (n : Bigint.t) (w : Bigint.t) : value =
  VBit(w, of_twos_complement n w)

and int_of_rawint (n : Bigint.t) (w : Bigint.t) : value =
  VInt(w, to_twos_complement n w)

and of_twos_complement (n : Bigint.t) (w : Bigint.t) : Bigint.t =
  let w' = power_of_two w in
  if Bigint.(n >= w')
  then Bigint.(n % w')
  else if Bigint.(n < zero)
  then of_twos_complement Bigint.(n + w') w
  else n

and to_twos_complement (n : Bigint.t) (w : Bigint.t) : Bigint.t =
  let two = Bigint.(one + one) in
  let w' = power_of_two w in
  if Bigint.(n >= (w' / two))
  then to_twos_complement Bigint.(n-w') w
  else if Bigint.(n < -(w'/two))
  then to_twos_complement Bigint.(n+w') w
  else n

(*----------------------------------------------------------------------------*)
(* Membership Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_struct_mem (env : EvalEnv.t) (name : string)
    (fs : (string * value) list) : EvalEnv.t * signal * value =
  (env, SContinue, List.Assoc.find_exn fs name ~equal:(=))

and eval_header_mem (env : EvalEnv.t) (fname : string) (e : Expression.t)
    (fs : (string * value) list) (valid : bool) : EvalEnv.t * signal * value =
  match fname with
  | "isValid"
  | "setValid"
  | "setInvalid" -> (env, SContinue, VBuiltinFun(fname, lvalue_of_expr e))
  | _            -> (env, SContinue, List.Assoc.find_exn fs fname ~equal:(=))

and eval_stack_mem (env : EvalEnv.t) (fname : string) (e : Expression.t)
    (hdrs : value list) (size : Bigint.t)
    (next : Bigint.t) : EvalEnv.t * signal * value =
  match fname with
  | "size"       -> eval_stack_size env size
  | "next"       -> eval_stack_next env hdrs size next
  | "last"       -> eval_stack_last env hdrs size next
  | "lastIndex"  -> eval_stack_lastindex env next
  | "pop_front"
  | "push_front" -> eval_stack_builtin env fname e
  | _ -> failwith "stack member unimplemented"

and eval_runtime_mem (env : EvalEnv.t) (mname : string) (expr : Expression.t)
    (v : vruntime) : EvalEnv.t * signal * value =
  match v with
  | PacketIn p -> eval_packet_in_mem env mname expr p
  | PacketOut p -> eval_packet_out_mem env mname expr p

and eval_stack_size (env : EvalEnv.t)
    (size : Bigint.t) : EvalEnv.t * signal * value =
  let five = Bigint.(one + one + one + one + one) in
  let thirty_two = shift_bigint_left Bigint.one five in
  (env, SContinue, VBit(thirty_two, size))

and eval_stack_next (env : EvalEnv.t) (hdrs : value list) (size : Bigint.t)
    (next : Bigint.t) : EvalEnv.t * signal * value =
  let (env', s, hdr) =
    if Bigint.(next >= size)
    then (EvalEnv.set_error "StackOutOfBounds" env, SReject, VNull)
    else (env, SContinue, List.nth_exn hdrs Bigint.(to_int_exn next)) in
  (env', s, hdr)

and eval_stack_last (env : EvalEnv.t) (hdrs : value list) (size : Bigint.t)
    (next : Bigint.t) : EvalEnv.t * signal *  value =
  let (env', s, hdr) =
    if Bigint.(next < one) || Bigint.(next > size)
    then (EvalEnv.set_error "StackOutOfBounds" env, SReject, VNull)
    else (env, SContinue, List.nth_exn hdrs Bigint.(to_int_exn next)) in
  (env', s, hdr)

and eval_stack_lastindex (env : EvalEnv.t)
    (next : Bigint.t) : EvalEnv.t * signal * value =
  let five = Bigint.(one + one + one + one + one) in
  let thirty_two = shift_bigint_left Bigint.one five in
  (env, SContinue, VBit(thirty_two, Bigint.(next - one)))

and eval_stack_builtin (env : EvalEnv.t) (fname : string)
    (e : Expression.t) : EvalEnv.t * signal * value =
  (env, SContinue, VBuiltinFun(fname, lvalue_of_expr e))

and eval_packet_in_mem (env : EvalEnv.t) (mname : string) (expr : Expression.t)
    (p : packet_in) : EvalEnv.t * signal * value =
  match mname with
  | "extract"   -> (env, SContinue, VBuiltinFun(mname, lvalue_of_expr expr))
  | "length"    -> (env, SContinue, VBuiltinFun(mname, lvalue_of_expr expr))
  | "lookahead" -> (env, SContinue, VBuiltinFun(mname, lvalue_of_expr expr))
  | "advance"   -> (env, SContinue, VBuiltinFun(mname, lvalue_of_expr expr))
  | _ -> failwith "packet member undefined"

and eval_packet_out_mem (env : EvalEnv.t) (mname : string) (expr : Expression.t)
    (p : packet_out) : EvalEnv.t * signal * value =
  match mname with
  | "emit" -> (env, SContinue, VBuiltinFun(mname, lvalue_of_expr expr))
  | _ -> failwith "packet out member undefined"

(*----------------------------------------------------------------------------*)
(* Function and Method Call Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_funcall' (env : EvalEnv.t) (params : Parameter.t list)
    (args : Argument.t list) (body : Block.t) : EvalEnv.t * signal * value =
  let (fenv, s) = copyin env params args in
  let (fenv', sign) = eval_block fenv SContinue body in
  let final_env = copyout fenv' params args in
  match sign with
  | SReject -> (final_env, SReject, VNull)
  | SReturn v -> (final_env, SContinue, v)
  | SContinue -> (final_env, SContinue, VNull)
  | SExit -> (final_env, SExit, VNull)

and copyin (env : EvalEnv.t) (params : Parameter.t list)
    (args : Argument.t list) : EvalEnv.t * signal =
  let f i (env,sign) e =
    Parameter.(
      let p = snd (List.nth_exn params i) in
      let ((env',s,v), n) = match snd e with
        | Argument.Expression {value=expr} ->
          (eval_expression' env SContinue expr, snd p.variable)
        | Argument.KeyValue {value=expr;key=(_,n)} ->
          (eval_expression' env SContinue expr, n)
        | Argument.Missing ->
          (eval_expression' env SContinue (assert_some p.opt_value), snd p.variable) in
      match (sign,s) with
      | SContinue,SContinue -> ((env',s), (n,v))
      | SReject, _ -> ((env,sign),(n,VNull))
      | _,SReject -> ((env',s),(n,VNull))
      | _ -> failwith "unreachable") in
  let fenv = EvalEnv.push_scope env in
  let ((fenv',s),arg_vals) = List.fold_mapi args ~f:f ~init:(fenv,SContinue) in
  let g e (p : Parameter.t) (n,v) =
    let name = n in
    let v' = match v with
      | VHeader (n,l,b) -> VHeader (name, l, b)
      | VStruct (n,l) -> VStruct (name,l)
      | _ -> v in
    match (snd p).direction with
    | None -> e
              |> EvalEnv.insert_val_firstlevel (snd (snd p).variable) v'
              |> EvalEnv.insert_typ_firstlevel (snd (snd p).variable) (snd p).typ
    | Some x -> begin match snd x with
        | InOut
        | In ->
          e
          |> EvalEnv.insert_val_firstlevel (snd (snd p).variable) v'
          |> EvalEnv.insert_typ_firstlevel (snd (snd p).variable) (snd p).typ
        | Out -> e end in
  let fenv' = List.fold2_exn params arg_vals ~init:fenv' ~f:g in
  match s with
  | SContinue -> (fenv',s)
  | SReject -> (fenv',s)
  | _ -> failwith " unreachable"

and copyout (fenv : EvalEnv.t) (params : Parameter.t list)
    (args : Argument.t list) : EvalEnv.t =
  let env = EvalEnv.pop_scope fenv in
  let h e (p:Parameter.t) a =
    match (snd p).direction with
    | None ->
     begin match snd (snd p).typ with 
        | TypeName(_,n) 
        | TopLevelType(_,n) -> 
          begin match print_endline "got here"; print_endline n; snd (EvalEnv.find_decl_toplevel n e) with 
            | ExternObject _ -> 
              let v = print_endline "got here next"; EvalEnv.find_val (snd (snd p).variable) fenv in
              begin match snd a with
                | Argument.Expression {value=expr}
                | Argument.KeyValue {value=expr;_} -> fst (eval_assign' e (lvalue_of_expr expr) v)
                | Argument.Missing -> e end
            | _ -> e end
        | _ -> e end
    | Some x -> begin match snd x with
        | InOut
        | Out ->
          let v = EvalEnv.find_val (snd (snd p).variable) fenv in
          begin match snd a with
            | Argument.Expression {value=expr}
            | Argument.KeyValue {value=expr;_} -> fst (eval_assign' e (lvalue_of_expr expr) v)
            | Argument.Missing -> e end
        | In -> e end in
  List.fold2_exn params args ~init:env ~f:h
  |> EvalEnv.set_error (EvalEnv.get_error fenv)

(*----------------------------------------------------------------------------*)
(* Built-in Function Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_builtin (env : EvalEnv.t) (name : string) (lv : lvalue)
    (args : Argument.t list) (ts : Type.t list) : EvalEnv.t * signal * value =
  match name with
  | "isValid"    -> eval_isvalid env lv
  | "setValid"   -> eval_setbool env lv true
  | "setInvalid" -> eval_setbool env lv false
  | "pop_front"  -> eval_popfront env lv args
  | "push_front" -> eval_pushfront env lv args
  | "extract"    -> eval_extract env lv args ts
  | "emit"       -> eval_emit env lv args
  | "length"     -> eval_length env lv
  | "lookahead"  -> eval_lookahead env lv ts
  | "advance"    -> eval_advance env lv args
  | "apply"      -> let (s,v) = value_of_lvalue env lv in eval_app env s v args
  | "verify"     -> eval_verify env args
  | _ -> failwith "builtin unimplemented"

and eval_isvalid (env : EvalEnv.t) (lv : lvalue) : EvalEnv.t * signal * value =
  let (s,v) = value_of_lvalue env lv in
  match s with
  | SContinue ->
    begin match lv with
      | LName _
      | LTopName _
      | LBitAccess _
      | LArrayAccess _ ->
        begin match v with
          | VHeader(_,_,b) -> (env, s, VBool b)
          | _ -> failwith "isvalid call is not a header" end
      | LMember(lv',n) ->
        let (s',v') = value_of_lvalue env lv' in
        begin match s' with
          | SContinue ->
            begin match v' with
              | VUnion(_,_,l) -> (env, s', VBool (List.Assoc.find_exn l n ~equal:(=)))
              | _ ->
                begin match v with
                  | VHeader(_,_,b) -> (env, s', VBool b)
                  | _ -> failwith "isvalid call is not a header" end end
          | SReject -> (env, s', VNull)
          | _ -> failwith "unreachable" end end
  | SReject -> (EvalEnv.set_error "StackOutOfBounds" env, s, VNull)
  | _ -> failwith "unreachable"

and eval_setbool (env : EvalEnv.t) (lv : lvalue)
    (b : bool) : EvalEnv.t * signal * value =
  match lv with
  | LName n ->
    begin match EvalEnv.find_val n env with
      | VHeader (n',fs,_) ->
        let env' = fst (eval_assign' env lv (VHeader(n',fs,b))) in
        (env', SContinue, VNull)
      | _ -> failwith "not a header" end
  | LTopName n ->
    begin match EvalEnv.find_val_toplevel n env with
      | VHeader (n',fs,_) ->
        let env' = fst (eval_assign' env lv (VHeader(n',fs,b))) in
        (env', SContinue, VNull)
      | _ -> failwith "not a header" end
  | LMember(lv', n2) ->
    let (s,v') = value_of_lvalue env lv' in
    begin match s with
      | SContinue ->
        begin match v' with
          | VUnion (n1, fs, vs) ->
            let vs' = List.map vs ~f:(fun (a,_) -> (a,if b then a=n2 else b)) in
            let env' = fst (eval_assign' env lv' (VUnion(n1, fs, vs'))) in
            (env', SContinue, VNull)
          | VStruct(n1, fs) -> failwith "unimplemented"
          | _ -> failwith "not a union" end
      | SReject -> (EvalEnv.set_error "StackOutOfBounds" env, s, VNull)
      | _ -> failwith "unreachable" end
  | LArrayAccess(lv', e) ->
    let (s,v') = value_of_lvalue env lv' in
    begin match s with
      | SContinue ->
        begin match v' with
          | VStack(n1,hdrs,size,next) ->
            let (env', s, i) = eval_expression' env SContinue e in
            let i' = bigint_of_val i in
            let (hdrs1, hdrs2) = List.split_n hdrs (Bigint.to_int_exn i') in
            let hdrs' = match hdrs2 with
              | VHeader(n2,vs,_) :: t -> hdrs1 @ (VHeader(n2,vs,b) :: t)
              | _ -> failwith "not a header" in
            begin match s with
              | SContinue ->
                let env'' = fst (eval_assign' env' lv' (VStack(n1,hdrs',size,next))) in
                (env'', SContinue, VNull)
              | SReject -> (env', s, VNull)
              | _ -> failwith "unreachable" end
          | _ -> failwith "not a stack" end
      | SReject -> (EvalEnv.set_error "StackOutOfBounds" env, s , VNull)
      | _ -> failwith "unreachable" end
  | LBitAccess _ -> failwith "not a header"

and eval_popfront (env : EvalEnv.t) (lv : lvalue)
    (args : Argument.t list) : EvalEnv.t * signal * value =
  eval_push_pop env lv args false

and eval_pushfront (env : EvalEnv.t) (lv : lvalue)
    (args : Argument.t list) : EvalEnv.t * signal * value =
  eval_push_pop env lv args true

and eval_extract (env : EvalEnv.t) (lv : lvalue) (args : Argument.t list)
    (ts : Type.t list) : EvalEnv.t * signal * value =
  match args with
  | [(_,Argument.Expression{value})]
  | [(_,Argument.KeyValue{value;_})]-> eval_extract' env lv value Bigint.zero
  | [(_,Argument.Expression{value=e1}); (_,Argument.Expression{value=e2})]
  | [(_,Argument.KeyValue{value=e1;key=(_,"variableSizeHeader")});
     (_,Argument.KeyValue{value=e2;key=(_,"variableFieldSizeInBits")})]
  | [(_,Argument.KeyValue{value=e2;key=(_,"variableFieldSizeInBits")});
     (_,Argument.KeyValue{value=e1;key=(_,"variableSizeHeader")})] ->
    let (env', s, b') = eval_expression' env SContinue e2 in
    let n = bigint_of_val b' in
    begin match s with
      | SContinue -> eval_extract' env' lv e1 n
      | SReject -> (env',s,VNull)
      | _ -> failwith "unreachable" end
  | [(_,Argument.Missing)] ->
    let t = match ts with
      | [x] -> x
      | _ -> failwith "invalid type args for extract" in
    eval_advance' env lv (width_of_typ env t)
  | _ -> failwith "wrong number of args for extract"

and eval_emit (env : EvalEnv.t) (lv : lvalue)
    (args : Argument.t list) : EvalEnv.t * signal * value =
  let args' = match args with
    | [a] -> List.map args ~f:snd
    | _ -> failwith "invalid emit args" in
  let expr = match args' with
    | [Argument.Expression{value}]
    | [Argument.KeyValue{value=value;_}] -> value
    | _ -> failwith "invalid emit args" in
  let lemit = lvalue_of_expr expr in
  let (env',s,_) = eval_expression' env SContinue expr in (* TODO  *)
  let (s',v) = lv |> value_of_lvalue env in
  let p = v |> assert_runtime |> assert_packet_out in
  let (env'', s'', p') = emit_lval env' p lemit in
  let env''' = fst (eval_assign' env'' lv (VRuntime(PacketOut p'))) in
  match s,s',s'' with
  | SContinue,SContinue,SContinue -> (env''', s, VNull)
  | SReject,_,_ -> (env, s, VNull)
  | _,SReject,_ -> (EvalEnv.set_error "StackOutOfBounds" env',s',VNull)
  | _,_,SReject -> (env'',s'',VNull)
  | _ -> failwith "unreachable"

and eval_length (env : EvalEnv.t) (lv : lvalue) : EvalEnv.t * signal * value =
  let (s,v) = value_of_lvalue env lv in
  let p = v |> assert_runtime |> assert_packet_in in
  match s with
  | SContinue ->
    (env, s, VBit (Bigint.of_int 32, p |> Cstruct.len |> Bigint.of_int))
  | SReject -> (EvalEnv.set_error "StackOutOfBounds" env, s, VNull)
  | _ -> failwith "unreachable"

and eval_lookahead (env : EvalEnv.t) (lv : lvalue)
    (ts : Type.t list) : EvalEnv.t * signal * value =
  let t = match ts with
    | [t] -> t
    | _ -> failwith "invalid lookahead type args" in
  let w = width_of_typ env t in
  let (s,v) = lv |> value_of_lvalue env in
  match s with
  | SContinue ->
    let p = v |> assert_runtime |> assert_packet_in in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    begin try
        let (p',_) = Cstruct.split ~start:0 p Bigint.(to_int_exn (w/eight)) in
        let (_,n,_) = bytes_of_packet p' Bigint.(w/eight) in
        (env, SContinue, val_of_bigint env w n (init_val_of_typ env "" t) t)
      with Invalid_argument _ ->
        (EvalEnv.set_error "PacketTooShort" env, SReject, VNull) end
  | SReject -> (EvalEnv.set_error "StackOutOfBounds" env ,s,VNull)
  | _ -> failwith "unreachable"

and eval_advance (env : EvalEnv.t) (lv : lvalue)
    (args : Argument.t list) : EvalEnv.t * signal * value =
  let args' = List.map args ~f:snd in
  let expr = match args' with
    | [Argument.Expression{value}]
    | [Argument.KeyValue{value;_}] -> value
    | _ -> failwith "invalid advance args" in
  let (env',s,v) = eval_expression' env SContinue expr in
  let n = v |> bigint_of_val in
  match s with
  | SContinue -> eval_advance' env' lv n
  | SReject -> (EvalEnv.set_error "StackOutOfBounds" env', s, VNull)
  | _ -> failwith "unreachable"

and eval_advance' (env : EvalEnv.t) (lv : lvalue)
    (n : Bigint.t) : EvalEnv.t * signal * value =
  let (s,v) = value_of_lvalue env lv in
  let p = v |> assert_runtime |> assert_packet_in in
  match s with
  | SContinue ->
    begin try
        let x = n |> Bigint.to_int_exn |> (/) 8 in
        let p' = Cstruct.split p x |> snd in
        let env' = fst (eval_assign' env lv (VRuntime(PacketIn p'))) in
        (env', SContinue, VNull)
      with Invalid_argument _ ->
        (EvalEnv.set_error "PacketTooShort" env, SReject, VNull) end
  | SReject -> (env,s,VNull)
  | _ -> failwith "unreachable"

and eval_verify (env : EvalEnv.t) (args : Argument.t list)
  : EvalEnv.t * signal * value =
  let exp_of_arg (arg : Argument.pre_t) =
    match arg with
    | Expression {value} -> value
    | _ -> failwith "arg is not an expression" in
  match args with
  | b :: err :: [] -> let (env', _, v) = eval_expression' env SContinue (snd b |> exp_of_arg) in
    begin match v with
    | VBool true -> (env', SContinue, VNull)
    | VBool false -> let (env'', _, v') = eval_expression' env' SContinue (snd err |> exp_of_arg) in
                     begin match v' with
                     | VError e -> (EvalEnv.set_error e env'', SReject, VNull)
                     | _ -> failwith "verify expected error"
                     end
    | _ -> failwith "verify expected bool"
    end
  | _ -> failwith "verify improper args"

and eval_push_pop (env : EvalEnv.t) (lv : lvalue)
    (args : Argument.t list) (b : bool) : EvalEnv.t * signal * value =
  let (env',s, a) = eval_push_pop_args env args in
  let (s',v) = value_of_lvalue env lv in
  let (n, hdrs, size, next) =
    match v with
    | VStack(n,hdrs,size,next) -> (n,hdrs,size,next)
    | _ -> failwith "push call not a header stack" in
  let x = if b then Bigint.(size - a) else a in
  let (hdrs1, hdrs2) = List.split_n hdrs Bigint.(to_int_exn x) in
  let t = typ_of_stack_mem env lv in
  let hdrs0 = List.init (Bigint.to_int_exn a) ~f:(fun x -> init_val_of_typ env (string_of_int x) t) in
  let hdrs' = if b then hdrs0 @ hdrs1 else hdrs2 @ hdrs0 in
  let y = if b then Bigint.(next + a) else Bigint.(next-a) in
  let v = VStack(n,hdrs',size,y) in
  match s,s' with
  | SContinue, SContinue -> (fst (eval_assign' env lv v), s, VNull)
  | SReject, _ -> (env',s,VNull)
  | _,SReject -> (EvalEnv.set_error "StackOutOfBounds" env',s',VNull)
  | _ -> failwith "unreachble"

and eval_push_pop_args (env : EvalEnv.t)
    (args : Argument.t list) : EvalEnv.t * signal * Bigint.t =
  let args' = List.map args ~f:snd in
  match args' with
  | [Argument.Expression{value}]
  | [Argument.KeyValue{value=value;_}] ->
    let (env', s, v) = eval_expression' env SContinue value in
    begin match s with
      | SContinue -> (env', s, bigint_of_val v)
      | SReject -> (env', s, Bigint.zero)
      | _ -> failwith "unreachable" end
  | _ -> failwith "invalid push or pop args"

and eval_extract' (env : EvalEnv.t) (lv : lvalue)
    (expr : Expression.t) (w : Bigint.t) : EvalEnv.t * signal * value =
  let (env', s, v) = eval_expression' env SContinue expr in
  match s with
  | SContinue ->
    let lhdr = lvalue_of_expr expr in
    let t = typ_of_lvalue env' lhdr in
    let d = decl_of_typ env' t in
    let (name,_,_) = assert_header v in
    let v' = init_val_of_typ env name t in
    let (s,v) = lv |> value_of_lvalue env' in
    let p = v |> assert_runtime |> assert_packet_in in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    let nbytes = Bigint.(nbytes_of_hdr env' d + w / eight)in
    let (p',n,s') = bytes_of_packet p nbytes in
    begin match s with
      | SContinue ->
        begin match s' with
          | SReject -> (EvalEnv.set_error "PacketTooShort" env',s',VNull)
          | SContinue ->
            let (name,fs,_) = assert_header v' in
            let (ns, vs) = List.unzip fs in
            let ((_,s),vs') =
              List.fold_map vs ~init:(Bigint.(nbytes * eight, n), SContinue) ~f:(extract_hdr_field w) in
            begin match s with
              | SReject -> (EvalEnv.set_error "HeaderTooShort" env',s,VNull)
              | SContinue ->
                let fs' = List.zip_exn ns vs' in
                let (env'',s') = eval_assign' env' lhdr (VHeader(name,fs',true)) in
                begin match s' with
                  | SContinue ->
                    (fst (eval_assign' env'' lv (VRuntime(PacketIn p'))), s', VNull)
                  | SReject -> (EvalEnv.set_error "StackOutOfBounds" env', s',VNull)
                  | _ -> failwith "unreachable" end
              | _ -> failwith "unreachable" end
          | _ -> failwith "unreachable" end
      | SReject -> (EvalEnv.set_error "StackOutOfBounds" env', s, VNull)
      | _ -> failwith "unreachable" end
  | SReject -> (env',s,VNull)
  | _ -> failwith "unreachable"

and extract_hdr_field (nvarbits : Bigint.t) (x : (Bigint.t * Bigint.t) * signal)
    (v : value) : ((Bigint.t * Bigint.t) * signal) * value =
  let (n,s) = x in
  match s with
  | SContinue ->
    begin match v with
      | VBit(w,_) -> extract_bit n w
      | VInt(w,_) -> extract_int n w
      | VVarbit(w,_,_) -> extract_varbit nvarbits n w
      | _ -> failwith "invalid header field type" end
  | SReject -> ((n,s),VNull)
  | _ -> failwith "unreachable"

and extract_bit (n : Bigint.t * Bigint.t)
    (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
  let (nw,nv) = n in
  let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-w) in
  let y = bitstring_slice nv Bigint.(nw-w-one) Bigint.zero in
  Bigint.(((nw-w, y), SContinue), VBit(w,x))

and extract_int (n : Bigint.t * Bigint.t)
    (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
  let (nw,nv) = n in
  let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-w) in
  let y = bitstring_slice nv Bigint.(nw-w-one) Bigint.zero in
  Bigint.(((nw-w, y), SContinue), VInt(w,to_twos_complement x w))

and extract_varbit (nbits : Bigint.t) (n : Bigint.t * Bigint.t)
    (w : Bigint.t) : ((Bigint.t * Bigint.t) * signal) * value =
  let (nw,nv) = n in
  if Bigint.(nbits > w)
  then ((n,SReject),VNull)
  else
    let x = bitstring_slice nv Bigint.(nw-one) Bigint.(nw-nbits) in
    let y = bitstring_slice nv Bigint.(nw-nbits-one) Bigint.zero in
    Bigint.(((nw-nbits, y), SContinue), VVarbit(w,nbits,x))

and emit_lval (env : EvalEnv.t) (p : packet_out)
    (lv : lvalue) : EvalEnv.t * signal * packet_out =
  let (s,v) = value_of_lvalue env lv in
  match s with
  | SContinue ->
    begin match v with
      | VStruct(_,fs)    -> emit_struct env p lv fs
      | VHeader(_,fs,b)  -> (env, s, emit_header env p lv fs b)
      | VUnion(_,v,bs)   -> emit_union env p lv v bs
      | VStack(_,hs,_,_) -> emit_stack env p lv hs
      | _ -> failwith "emit undefined on type" end
  | SReject -> (EvalEnv.set_error "StackOutOfBounds" env, s, p)
  | _ -> failwith "unreachable"

and emit_struct (env : EvalEnv.t) (p : packet_out) (lv : lvalue)
    (fs :(string * value) list) : EvalEnv.t * signal * packet_out =
  let fs' = reset_fields env lv fs in
  let h (e,s,p) (n,v) =
    match s with
    | SContinue -> emit_lval e p (LMember(lv,n))
    | SReject -> (e,s,p)
    | _ -> failwith "unreachable" in
  List.fold_left fs' ~init:(env, SContinue, p) ~f:h

and emit_header (env : EvalEnv.t) (p : packet_out) (lv : lvalue)
    (fs : (string * value) list) (b : bool) : packet_out =
  if b
  then
    let fs' = reset_fields env lv fs in
    let fs'' = List.map fs' ~f:snd in
    let d = decl_of_typ env (typ_of_lvalue env lv) in
    let f n v =
      match v with
      | VBit(w,v) -> Bigint.(n * power_of_two w + v)
      | VInt(w,v) -> Bigint.(n * power_of_two w + (of_twos_complement v w))
      | VVarbit(_,w,v) -> Bigint.(n * power_of_two w + v)
      | _ -> failwith "invalid header field type" in
    let n = List.fold_left fs'' ~init:Bigint.zero ~f:f in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    let w = Bigint.(nbytes_of_hdr env d * eight) in
    let p1 = packet_of_bytes n w in
    let (p0,p2) = p in
    (Cstruct.append p0 p1,p2)
  else p

and emit_union (env : EvalEnv.t) (p : packet_out) (lv : lvalue) (v : value)
    (vs : (string * bool) list) : EvalEnv.t * signal * packet_out =
  if List.exists vs ~f:snd
  then
    let vs' = List.map vs ~f:(fun (a,b) -> (b,a)) in
    let n = List.Assoc.find_exn vs' ~equal:(=) true in
    emit_lval env p (LMember(lv, n))
  else (env, SContinue, p)

and emit_stack (env : EvalEnv.t) (p : packet_out) (lv : lvalue)
    (hs : value list) : EvalEnv.t * signal * packet_out =
  let f (e,s,p,n) v =
    let lv' = (LArrayAccess(lv, (Info.dummy, Expression.Int(Info.dummy,
                                                            {value = n;
                                                             width_signed = None})))) in
    let (e',s',p') = emit_lval env p lv' in
    match s with
    | SContinue -> (e',s',p', Bigint.(n + one))
    | SReject -> (e,s,p,Bigint.(n + one))
    | _ -> failwith "unreachable" in
  let (a,b,c,d) =  List.fold_left hs ~init:(env,SContinue,p,Bigint.zero) ~f:f in
  (a,b,c)

and width_of_typ (env : EvalEnv.t) (t : Type.t) : Bigint.t =
  match snd t with
  | Bool -> Bigint.one
  | IntType e -> e |> eval_expression' env SContinue |> thrd3 |> bigint_of_val
  | BitType e -> e |> eval_expression' env SContinue |> thrd3 |> bigint_of_val
  | TopLevelType _
  | TypeName _ -> width_of_decl env (decl_of_typ env t)
  | HeaderStack{header=t';size=e} -> width_of_stack env t' e
  | Tuple l -> width_of_tuple env l
  | Void | DontCare -> Bigint.zero
  | Error | VarBit _ -> failwith "type does not a have a fixed width"
  | SpecializedType _ -> failwith "unimplemented"

and width_of_tuple (env : EvalEnv.t) (l : Type.t list) : Bigint.t =
  let l' = List.map l ~f:(width_of_typ env) in
  List.fold_left l' ~init:Bigint.zero ~f:Bigint.(+)

and width_of_stack (env : EvalEnv.t) (t : Type.t)
    (e : Expression.t) : Bigint.t =
  Bigint.(
    e
    |> eval_expression' env SContinue
    |> thrd3
    |> bigint_of_val
    |> ( * ) (width_of_typ env t))

and width_of_hdr (env : EvalEnv.t) (fs : Declaration.field list) : Bigint.t =
  let ts = List.map fs ~f:(fun f -> (snd f).typ) in
  let ws = List.map ts ~f:(width_of_typ env) in
  List.fold_left ws ~init:Bigint.zero ~f:Bigint.(+)

and width_of_decl (env : EvalEnv.t) (d : Declaration.t) : Bigint.t =
  match snd d with
  | Header{fields;_} -> width_of_hdr env fields
  | Struct{fields;_} -> width_of_hdr env fields
  | SerializableEnum{typ;_} -> width_of_typ env typ
  | TypeDef{typ_or_decl;_}
  | NewType{typ_or_decl;_} ->
    begin match typ_or_decl with
      | Left t -> width_of_typ env t
      | Right d -> width_of_decl env d end
  | _ -> failwith "decl does not have a fixed width"

and width_of_val (v : value) : Bigint.t =
  match v with
  | VBit (w,v) | VInt (w,v) -> w
  | VInteger _ -> failwith "width of VInteger"
  | _ -> failwith "unimplemented"

and val_of_bigint (env : EvalEnv.t) (w : Bigint.t) (n : Bigint.t) (v : value)
    (t : Type.t) : value =
  match v with
  | VNull              -> VNull
  | VBool _            -> VBool Bigint.(bitstring_slice n one zero = one)
  | VBit _             -> VBit(w,n)
  | VInt _             -> VInt(w,to_twos_complement n w)
  | VTuple l           -> tuple_of_bigint env w n t l
  | VStruct(_,fs)      -> struct_of_bigint env w n t fs
  | VHeader(_,fs,_)    -> header_of_bigint env w n t fs
  | VStack(_,vs,s,n)   -> stack_of_bigint env w n t vs s n
  | VSenumField(a,b,v) -> VSenumField(a,b,val_of_bigint env w n v t)
  | VInteger _
  | VVarbit _
  | VSet _
  | VString _
  | VError _
  | VMatchKind
  | VFun _
  | VBuiltinFun _
  | VAction _
  | VUnion _
  | VEnumField _
  | VExternFun _
  | VExternObject _
  | VRuntime _
  | VParser _
  | VControl _
  | VPackage _
  | VTable _           -> failwith "value does not have a fixed width"

and tuple_of_bigint (env : EvalEnv.t) (w : Bigint.t) (n : Bigint.t)
    (t : Type.t) (l : value list) : value =
  let f i (w,n) v =
    let t' = typ_of_tuple_field t i in
    let wv = width_of_typ env t' in
    let nv = bitstring_slice n Bigint.(w-one) Bigint.(w-wv) in
    let w' = Bigint.(w-wv) in
    let n' = bitstring_slice n Bigint.(w-wv-one) Bigint.zero in
    let v' = val_of_bigint env wv nv v t' in
    ((w',n'), v') in
  let l' = List.folding_mapi l ~init:(w,n) ~f:f in
  VTuple l'

and struct_of_bigint (env : EvalEnv.t) (w : Bigint.t) (n : Bigint.t)
    (t : Type.t) (fs : (string * value) list) : value =
  let f (w,n) (s,v) =
    let t' = typ_of_struct_field env t s in
    let wv = width_of_typ env t' in
    let nv = bitstring_slice n Bigint.(w-one) Bigint.(w-wv) in
    let w' = Bigint.(w-wv) in
    let n' = bitstring_slice n Bigint.(w-wv-one) Bigint.zero in
    let v' = val_of_bigint env wv nv v t' in
    ((w',n'),(s,v')) in
  let fs' = List.folding_map fs ~init:(w,n) ~f:f in
  VStruct("",fs')

and header_of_bigint (env : EvalEnv.t) (w : Bigint.t) (n : Bigint.t)
    (t : Type.t) (fs : (string * value) list) : value =
  let f (w,n) (s,v) =
    let t' = typ_of_header_field env t s in
    let wv = width_of_typ env t' in
    let nv = bitstring_slice n Bigint.(w-one) Bigint.(w-wv) in
    let w' = Bigint.(w-wv) in
    let n' = bitstring_slice n Bigint.(w-wv-one) Bigint.zero in
    let v' = val_of_bigint env wv nv v t' in
    ((w',n'),(s,v')) in
  let fs' = List.folding_map fs ~init:(w,n) ~f:f in
  VHeader("",fs',true)

and stack_of_bigint (env : EvalEnv.t) (w : Bigint.t) (n : Bigint.t)
    (t : Type.t) (vs : value list) (size : Bigint.t) (next : Bigint.t) : value =
  let t' = match snd t with
    | HeaderStack{header;_} -> header
    | _ -> failwith "not a header stack" in
  let f (w,n) v =
    let wv = width_of_typ env t' in
    let nv = bitstring_slice n Bigint.(w-one) Bigint.(w-wv) in
    let w' = Bigint.(w-wv) in
    let n' = bitstring_slice n Bigint.(w-wv-one) Bigint.zero in
    let v' = val_of_bigint env wv nv v t' in
    ((w',n'),v') in
  let vs' = List.folding_map vs ~init:(w,n) ~f:f in
  VStack("",vs',size,next)

(*----------------------------------------------------------------------------*)
(* Parser Evaluation *)
(*----------------------------------------------------------------------------*)

and eval_parser (env : EvalEnv.t) (params : Parameter.t list)
    (args : Argument.t list) (vs : (string * value) list)
    (locals : Declaration.t list) (states : Parser.state list) : EvalEnv.t * signal =
  let (penv, s) = copyin env params args in
  match s with
  | SContinue ->
    let f a (x,y) = EvalEnv.insert_val x y a in
    let penv' = List.fold_left vs ~init:penv ~f:f in
    let penv'' = List.fold_left locals ~init:penv' ~f:eval_decl in
    let states' = List.map states ~f:(fun s -> snd (snd s).name, s) in
    let start = List.Assoc.find_exn states' "start" ~equal:(=) in
    let (penv''',final_state) = eval_state_machine penv'' states' start in
    (copyout penv''' params args, final_state)
  | SReject -> (EvalEnv.pop_scope penv, SReject)
  | _ -> failwith "unreachable"

and eval_state_machine (env : EvalEnv.t) (states : (string * Parser.state) list)
    (state : Parser.state) : EvalEnv.t * signal =
  let (stms, transition) =
    match snd state with
    | {statements=stms; transition=t;_} -> (stms, t) in
  let stms' = (Info.dummy, Statement.BlockStatement
                 {block = (Info.dummy, {annotations = []; statements = stms})}) in
  let (env', sign) = eval_statement env SContinue stms' in
  match sign with
  | SContinue -> eval_transition env' states transition
  | SReject -> (env', SReject)
  | SReturn _ -> failwith "return statements not permitted in parsers"
  | SExit -> failwith "exit statements not permitted in parsers"

and eval_transition (env : EvalEnv.t) (states : (string * Parser.state) list)
    (transition : Parser.transition) : EvalEnv.t * signal =
  match snd transition with
  | Direct{next = (_, next)} -> eval_direct env states next
  | Select{exprs;cases} -> eval_select env states exprs cases

and eval_direct (env : EvalEnv.t) (states : (string * Parser.state) list)
    (next : string) : EvalEnv.t * signal =
  match next with
  | "accept" -> (env, SContinue)
  | "reject" -> (env, SReject)
  | _ -> let state = List.Assoc.find_exn states next ~equal:(=) in
        eval_state_machine env states state

and eval_select (env : EvalEnv.t) (states : (string * Parser.state) list)
    (exprs : Expression.t list) (cases : Parser.case list) : EvalEnv.t * signal =
  let f (env,s) e =
    let (a,b,c) = eval_expression' env s e in
    ((a,b),c) in
  let ((env', s), vs) = List.fold_map exprs ~init:(env,SContinue) ~f:f in
  let ws = List.map vs ~f:width_of_val in
  match s with
  | SContinue ->
    let g (e,s) set =
      let (x,y,z) = set_of_case e s set ws in
      ((x,y),(z,x)) in
    let ((env'',s), ss) = List.fold_map cases ~init:(env', SContinue) ~f:g in
    let ms = List.map ss ~f:(fun (x,y) -> (values_match_set vs x, y)) in
    let ms' = List.zip_exn ms cases
              |> List.map ~f:(fun ((b,env),c) -> (b,(env,c))) in
    let next = List.Assoc.find ms' true ~equal:(=) in
    begin match next with
      | None -> eval_direct (EvalEnv.set_error "NoMatch" env'') states "reject"
      | Some (fenv,next) ->
        let next' = snd (snd next).next in
        eval_direct fenv states next' end
  | SReject -> (env', SReject)
  | _ -> failwith "unreachable"

and set_of_case (env : EvalEnv.t) (s : signal)
    (case : Parser.case) (ws : Bigint.t list) : EvalEnv.t * signal * set =
  match s with
  | SContinue -> set_of_matches env s (snd case).matches ws
  | SReject   -> (env,s,SUniversal)
  | _ -> failwith "unreachable"

and set_of_matches (env : EvalEnv.t) (s : signal)
    (ms : Match.t list) (ws : Bigint.t list) : EvalEnv.t * signal * set =
  match ms,ws with
  | [],_ -> failwith "invalid set"
  | [m],[w] -> set_of_match env s m w
  | l,ws ->
    let f i (a,b) c =
      let (x,y,z) = set_of_match a b c (List.nth_exn ws i) in
      ((x,y),z) in
    let ((env',s),l') = List.fold_mapi l ~init:(env,SContinue) ~f:f in
    (env',s,SProd l')

and set_of_match (env : EvalEnv.t) (s : signal)
    (m : Match.t) (w : Bigint.t) : EvalEnv.t * signal * set =
  match s with
  | SContinue ->
    begin match snd m with
      | Default
      | DontCare         -> (env, SContinue, SUniversal)
      | Expression{expr} ->
        let (env', s, v) = eval_expression' env SContinue expr in
        (env', s, assert_set v w) end
  | SReject -> (env, s, SUniversal)
  | _ -> failwith "unreachable"

and values_match_set (vs : value list) (s : set) : bool =
  match s with
  | SSingleton (w,v)  -> values_match_singleton vs v
  | SUniversal    -> true
  | SMask(v1,v2)  -> values_match_mask vs v1 v2
  | SRange(v1,v2) -> values_match_range vs v1 v2
  | SProd l       -> values_match_prod vs l
  | SLpm(v1,_,v2) -> values_match_mask vs v1 v2

and values_match_singleton (vs : value list) (n : Bigint.t) : bool =
  let v = assert_singleton vs in
  v |> bigint_of_val |> (Bigint.(=) n)

and values_match_mask (vs : value list) (v1 : value) (v2 : value) : bool =
  let two = Bigint.(one + one) in
  let v = assert_singleton vs in
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

and values_match_range (vs : value list) (v1 : value) (v2 : value) : bool =
  let v = assert_singleton vs in
  match (v, v1, v2) with
  | VBit(w0,b0), VBit(w1,b1), VBit(w2,b2)
  | VInt(w0,b0), VInt(w1,b1), VInt(w2,b2) ->
    w0 = w1 && w1 = w2 && Bigint.(b1 <= b0 && b0 <= b2)
  | _ -> failwith "implicit casts unimplemented"

and values_match_prod (vs : value list) (l : set list) : bool =
  let bs = List.mapi l ~f:(fun i x -> values_match_set [List.nth_exn vs i] x) in
  List.for_all bs ~f:(fun b -> b)

(* -------------------------------------------------------------------------- *)
(* Control Evaluation *)
(* -------------------------------------------------------------------------- *)

and eval_control (env : EvalEnv.t) (params : Parameter.t list)
    (args : Argument.t list) (vs : (string * value) list)
    (locals : Declaration.t list) (apply : Block.t) : EvalEnv.t * signal =
  let (cenv,_) = copyin env params args in
  let f a (x,y) = EvalEnv.insert_val x y a in
  let cenv' = List.fold_left vs ~init:cenv ~f:f in
  let cenv'' = List.fold_left locals ~init:cenv' ~f:eval_decl in
  let block = (Info.dummy, Statement.BlockStatement {block = apply}) in
  let (cenv''', sign) = eval_statement cenv'' SContinue block in
  match sign with
  | SContinue
  | SExit     -> (copyout cenv''' params args, sign)
  | SReject   -> failwith "control should not reject"
  | SReturn _ -> failwith "control should not return"

(*----------------------------------------------------------------------------*)
(* Helper functions *)
(*----------------------------------------------------------------------------*)

and snd3 (a,b,c) = b

and assert_singleton (vs : value list) : value =
  match vs with
  | [v] -> v
  | _ -> failwith "value list has more than one element"

and assert_bool (v : value) : bool =
  match v with
  | VBool b -> b
  | _ -> failwith "not a bool"

and assert_rawint (v : value) : Bigint.t =
  match v with
  | VInteger n -> n
  | _ -> failwith "not a raw int type"

and assert_bit (v : value) : Bigint.t * Bigint.t =
  match v with
  | VBit(w,n) -> (w,n)
  | _ -> failwith "not a bitstring"

and assert_int (v : value) : Bigint.t * Bigint.t =
  match v with
  | VInt(w,n) -> (w,n)
  | _ -> failwith "not a signed bitstring"

and assert_varbit (v : value) : Bigint.t * Bigint.t * Bigint.t =
  match v with
  | VVarbit(fw,dw,n) -> (fw,dw,n)
  | _ -> failwith "not a varbit"

and assert_tuple (v : value) : value list =
  match v with
  | VTuple l -> l
  | _ -> failwith "not a tuple"

and assert_set (v : value) (w : Bigint.t) : set =
  match v with
  | VSet s -> s
  | VInteger i -> SSingleton (w,i)
  | VInt (_,i) -> SSingleton (w,i)
  | VBit (_,i) -> SSingleton (w,i)
  | _ -> failwith "not a set"

and assert_string (v : value) : string =
  match v with
  | VString s -> s
  | _ -> failwith "not a string"

and assert_error (v : value) : string =
  match v with
  | VError s -> s
  | _ -> failwith "not an error"

and assert_struct (v : value) : string * (string * value) list =
  match v with
  | VStruct(n,vs) -> (n,vs)
  | _ -> failwith "not a struct"

and assert_header (v : value) : string * (string * value) list * bool =
  match v with
  | VHeader (n,l,b) -> (n,l,b)
  | _ -> failwith "not a header"

and assert_stack (v : value) : (string * value list * Bigint.t * Bigint.t) =
  match v with
  | VStack(s,vs,size,n) -> (s,vs,size,n)
  | _ -> failwith "not a stack"

and assert_runtime (v : value) : vruntime =
  match v with
  | VRuntime r -> r
  | _ -> failwith "not a runtime value"

and assert_packet_in (p : vruntime) : packet_in =
  match p with
  | PacketIn x -> x
  | _ -> failwith "not a packet in"

and assert_packet_out (v : vruntime) : packet_out =
  match v with
  | PacketOut p -> p
  | _ -> failwith "not a packet_out"

and assert_some (x : 'a option) : 'a =
  match x with
  | None -> failwith "is none"
  | Some v -> v

and decl_of_typ (e : EvalEnv.t) (t : Type.t) : Declaration.t =
  match snd t with
  | TypeName (_,s)                 -> (EvalEnv.find_decl s e)
  | TopLevelType (_,s)             -> (EvalEnv.find_decl_toplevel s e)
  | _ -> (Info.dummy, Error{members = []}) (* TODO: find better solution *)

and init_binding_of_field (env : EvalEnv.t)
    (f : Declaration.field) : string * value =
  let n = snd (snd f).name in
  (n, init_val_of_typ env n (snd f).typ)

and bigint_of_val (v : value) : Bigint.t =
  match v with
  | VInt(_,n)
  | VBit(_,n)
  | VInteger n -> n
  | _ -> failwith "value not representable as bigint"

and power_of_two (w : Bigint.t) : Bigint.t =
  shift_bigint_left Bigint.one w

and bitstring_slice (n : Bigint.t) (m : Bigint.t) (l : Bigint.t) : Bigint.t =
  Bigint.(
    if l > zero
    then bitstring_slice (n/(one + one)) (m-one) (l-one)
    else n % (power_of_two (m + one)))

and typ_of_tuple_field (t : Type.t) (i : int) : Type.t =
  match snd t with
  | Tuple ts -> List.nth_exn ts i
  | _ -> failwith "not a tuple type"

and typ_of_struct_field (env : EvalEnv.t) (t : Type.t)
    (fname : string) : Type.t =
  let (_, d) = decl_of_typ env t in
  let fs = match d with
    | Struct h -> h.fields
    | _ -> failwith "not a struct" in
  match List.filter fs ~f:(fun a -> snd (snd a).name = fname) with
  | h :: _ -> (snd h).typ
  | _ -> failwith "field name not found"

and typ_of_header_field (env : EvalEnv.t) (t : Type.t)
    (fname : string) : Type.t =
  let (_,d) = decl_of_typ env t in
  let fs = match d with
    | Header h -> h.fields
    | _ -> failwith "not a header" in
  match List.filter fs ~f:(fun a -> snd (snd a).name = fname) with
  | h :: _ -> (snd h). typ
  | _ -> failwith "field name not found"

and typ_of_union_field (env : EvalEnv.t) (t : Type.t)
    (fname : string) : Type.t =
  let (_, d) = decl_of_typ env t in
  let fs = match d with
    | HeaderUnion u -> u.fields
    | _ -> failwith "not a union" in
  match List.filter fs ~f:(fun a -> snd (snd a).name = fname) with
  | h :: _ -> (snd h).typ
  | _ -> failwith "field name not found"

and typ_of_stack_mem (env : EvalEnv.t) (lv : lvalue) : Type.t =
  let t = typ_of_lvalue env lv in
  match snd t with
  | HeaderStack{header;_} -> header
  | _ -> failwith "not a header stack"

and struct_of_list (env : EvalEnv.t) (lv : lvalue) (name : string)
    (l : value list) : value =
  let t = typ_of_lvalue env lv in
  let d = decl_of_typ env t in
  let fs = match snd d with
    | Declaration.Struct s -> s.fields
    | _ -> failwith "not a struct" in
  let ns = List.map fs ~f:(fun x -> snd (snd x).name) in
  let ts = List.map fs ~f:(fun x -> (snd x).typ) in
  let l' = List.mapi l ~f:(fun i v -> implicit_cast_from_rawint env v (List.nth_exn ts i)) in
  let l'' = List.mapi l' ~f:(fun i v -> implicit_cast_from_tuple env
                                (LMember(lv, List.nth_exn ns i)) (List.nth_exn ns i)
                                v (List.nth_exn ts i)) in
  let l''' = List.mapi l'' ~f:(fun i v -> (List.nth_exn ns i, v)) in
  VStruct (name, l''')

and header_of_list (env : EvalEnv.t) (lv : lvalue) (name : string)
    (l : value list) : value =
  let t = typ_of_lvalue env lv in
  let d = decl_of_typ env t in
  let fs = match snd d with
    | Declaration.Header h -> h.fields
    | _ -> failwith "not a header" in
  let ns = List.map fs ~f:(fun x -> snd (snd x).name) in
  let ts = List.map fs ~f:(fun x -> (snd x).typ) in
  let l' = List.mapi l ~f:(fun i v -> implicit_cast_from_rawint env v (List.nth_exn ts i)) in
  let l'' = List.mapi l' ~f:(fun i v -> (List.nth_exn ns i, v)) in
  VHeader (name, l'', true)

and implicit_cast_from_rawint (env : EvalEnv.t) (v : value)
    (t : Type.t) : value =
  match v with
  | VInteger n ->
    begin match snd t with
      | Type.IntType e ->
        e
        |> eval_expression' env SContinue
        |> thrd3
        |> bigint_of_val
        |> int_of_rawint n
      | Type.BitType e ->
        e
        |> eval_expression' env SContinue
        |> thrd3
        |> bigint_of_val
        |> bit_of_rawint n
      | Type.Bool -> failwith "is bool"
      | Type.TypeName (_,n) ->
        EvalEnv.find_decl n env
        |> assert_typ_def
        |> assert_typ
        |> implicit_cast_from_rawint env v
      | _ -> failwith "attempt to assign raw int to wrong type"
      end
  | _ -> v

and assert_typ (typ_or_decl : (Type.t, Declaration.t) Util.alternative) : Type.t =
  match typ_or_decl with
  | Left typ -> typ
  | Right decl -> failwith "not a typ"

and assert_typ_def (typ : Declaration.t) : (Type.t, Declaration.t) Util.alternative =
  match snd typ with
  | TypeDef {typ_or_decl;_} -> typ_or_decl
  | _ -> failwith "not a typedef"

and implicit_cast_from_tuple (env : EvalEnv.t) (lv : lvalue) (n : string) (v : value)
    (t : Type.t) : value =
  match v with
  | VTuple l ->
    begin match snd (decl_of_typ env t) with
      | Struct _ -> struct_of_list env lv n l
      | Header _ -> header_of_list env lv n l
      | _ -> VTuple l end
  | _ -> v

and nbytes_of_hdr (env : EvalEnv.t) (d : Declaration.t) : Bigint.t =
  match snd d with
  | Header{fields = fs;_} ->
    let ts = List.map fs ~f:(fun f -> snd (snd f).typ) in
    let ls = List.map ts
        ~f:(function
            | Type.IntType e
            | Type.BitType e -> eval_expression' env SContinue e |> thrd3 |> bigint_of_val
            | Type.VarBit _ -> Bigint.zero
            | _ -> failwith "illegal header field type") in
    let n = List.fold_left ls ~init:Bigint.zero ~f:Bigint.(+) in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    Bigint.(n/eight)
  | _ -> failwith "not a header"

and bytes_of_packet (p : packet_in)
    (nbytes : Bigint.t) : packet_in * Bigint.t * signal =
  try
    let (c1,c2) = Cstruct.split p (Bigint.to_int_exn nbytes) in
    let s = Cstruct.to_string c1 in
    let chars = String.to_list s in
    let bytes = List.map chars ~f:Char.to_int in
    let bytes' = List.map bytes ~f:Bigint.of_int in
    let eight = Bigint.((one + one) * (one + one) * (one + one)) in
    let f a n = Bigint.(a * power_of_two eight + n) in
    let n = List.fold_left bytes' ~init:Bigint.zero ~f:f in
    (c2,n,SContinue)
  with Invalid_argument _ -> (p,Bigint.zero,SReject)

and packet_of_bytes (n : Bigint.t) (w : Bigint.t) : packet_in =
  let eight = Bigint.((one + one) * (one + one) * (one + one)) in
  let seven = Bigint.(eight - one) in
  let rec h acc n w =
    if Bigint.(w = zero) then acc else
      let lsbyte = bitstring_slice n seven Bigint.zero in
      let n' = bitstring_slice n Bigint.(w-one) eight in
      h (lsbyte :: acc) n' Bigint.(w-eight) in
  let bytes = h [] n w in
  let ints = List.map bytes ~f:Bigint.to_int_exn in
  let chars = List.map ints ~f:Char.of_int_exn in
  let s = String.of_char_list chars in
  Cstruct.of_string s

and reset_fields (env : EvalEnv.t) (lv : lvalue)
    (fs : (string * value) list) : (string * value) list =
  let f l (n,v) =
    if List.Assoc.mem l ~equal:(=) n
    then l
    else (n,v) :: l in
  let fs' = List.fold_left fs ~init:[] ~f:f in
  let init = init_val_of_typ env "" (typ_of_lvalue env lv) in
  let fs0 = match init with
    | VStruct(_,fs) -> fs
    | VHeader(_,fs,_) -> fs
    | _ -> failwith "not a struct or header" in
  let g (n,_) =
    (n, List.Assoc.find_exn fs' ~equal:(=) n) in
  List.map fs0 ~f:g

(* -------------------------------------------------------------------------- *)
(* Target and Architecture Dependent Evaluation *)
(* -------------------------------------------------------------------------- *)

let rec eval_main (env : EvalEnv.t) (pack : packet_in)
    (ctrl : Table.pre_entry list) : packet_in =
  let (_, obj, vs) =
    match EvalEnv.find_val "main" env with
    | VPackage ((info, obj), vs) -> (info, obj, vs)
    | _ -> failwith "main not a stateful object" in
  let name =
    match obj with
    | Declaration.PackageType {name=(_,n);_} -> n
    | _ -> failwith "main is no a package" in
  match name with
  | "ebpfFilter" -> eval_ebpfFilter env vs pack ctrl
  | "V1Switch" -> eval_v1switch env vs pack ctrl
  | "EmptyPackage" -> pack
  | _ -> failwith "architecture not supported"

and eval_ebpfFilter (env : EvalEnv.t) (vs : (string * value) list)
    (pack : packet_in) (ctrl : Table.pre_entry list) : packet_in =
  let parser = List.Assoc.find_exn vs "prs"  ~equal:(=) in 
  let filter = List.Assoc.find_exn vs "filt" ~equal:(=) in
  let params = 
    match parser with
    | VParser {pparams=ps;_} -> ps
    | _ -> failwith "parser is not a parser object" in
  let pckt = VRuntime (PacketIn pack) in
  let hdr = init_val_of_typ env "hdr" (snd (List.nth_exn params 1)).typ in
  let accept = VBool (false) in
  let env =
    EvalEnv.(env 
             |> insert_val "packet" pckt 
             |> insert_val "hdr"    hdr
             |> insert_val "accept" accept
             |> insert_typ "packet" (snd (List.nth_exn params 0)).typ
             |> insert_typ "hdr"    (snd (List.nth_exn params 1)).typ 
             |> insert_typ "accept" (Info.dummy, Type.Bool)
             |> insert_table_entries ctrl) in
  let pckt_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "packet"))}) in
  let hdr_expr = 
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "hdr"))}) in
  let accept_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "accept"))}) in
  let (env, state, _) =
    eval_app env SContinue parser [pckt_expr; hdr_expr] in
  let env = if state = SReject
    then
      eval_assign' env (LName("accept")) (VBool(false)) |> fst
    else env |> eval_ebpf_ctrl filter [hdr_expr; accept_expr] |> fst in
  print_endline "After runtime evaluation";
  EvalEnv.print_env env;
  match EvalEnv.find_val "packet" env with
  | VRuntime (PacketOut(p0,p1)) -> Cstruct.append p0 p1
  | _ -> failwith "pack not a packet"

and eval_v1switch (env : EvalEnv.t) (vs : (string * value) list)
    (pack : packet_in) (ctrl : Table.pre_entry list) : packet_in =
  let parser =
    List.Assoc.find_exn vs "p"   ~equal:(=) in
  let verify =
    List.Assoc.find_exn vs "vr"  ~equal:(=) in
  let ingress =
    List.Assoc.find_exn vs "ig"  ~equal:(=) in
  let egress =
    List.Assoc.find_exn vs "eg"  ~equal:(=) in
  let compute =
    List.Assoc.find_exn vs "ck"  ~equal:(=) in
  let deparser =
    List.Assoc.find_exn vs "dep" ~equal:(=) in
  let params =
    match parser with
    | VParser {pparams=ps;_} -> ps
    | _ -> failwith "parser is not a parser object" in
  let pckt = VRuntime (PacketIn pack) in
  let hdr =
    init_val_of_typ env "hdr"      (snd (List.nth_exn params 1)).typ in
  let meta =
    init_val_of_typ env "meta"     (snd (List.nth_exn params 2)).typ in
  let std_meta =
    init_val_of_typ env "std_meta" (snd (List.nth_exn params 3)).typ in
  let env =
    EvalEnv.(env
             |> insert_val "packet"   pckt
             |> insert_val "hdr"      hdr
             |> insert_val "meta"     meta
             |> insert_val "std_meta" std_meta
             |> insert_typ "packet"   (snd (List.nth_exn params 0)).typ
             |> insert_typ "hdr"      (snd (List.nth_exn params 1)).typ
             |> insert_typ "meta"     (snd (List.nth_exn params 2)).typ
             |> insert_typ "std_meta" (snd (List.nth_exn params 3)).typ
             |> insert_table_entries ctrl) in
  (* TODO: implement a more responsible way to generate variable names *)
  let pckt_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "packet"))}) in
  let hdr_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "hdr"))}) in
  let meta_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "meta"))}) in
  let std_meta_expr =
    (Info.dummy, Argument.Expression {value = (Info.dummy, Name (Info.dummy, "std_meta"))}) in
  let (env, state, _) =
    eval_app env SContinue parser [pckt_expr; hdr_expr; meta_expr; std_meta_expr] in
  let err = EvalEnv.get_error env in
  let env = if state = SReject
    then
      eval_assign' env (LMember(LName("std_meta"),"parser_error")) (VError(err)) |> fst
    else env in
  let pckt' =
    VRuntime (PacketOut(Cstruct.create 0, EvalEnv.find_val "packet" env
                                          |> assert_runtime
                                          |> assert_packet_in)) in
  let env = EvalEnv.insert_val "packet" pckt' env in
  let (env, _) = env
            |> eval_v1control verify   [hdr_expr; meta_expr] |> fst
            |> eval_v1control ingress  [hdr_expr; meta_expr; std_meta_expr] |> fst
            |> eval_v1control egress   [hdr_expr; meta_expr; std_meta_expr] |> fst
            |> eval_v1control compute  [hdr_expr; meta_expr] |> fst
            |> eval_v1control deparser [pckt_expr; hdr_expr] in
  print_endline "After runtime evaluation";
  EvalEnv.print_env env;
  match EvalEnv.find_val "packet" env with
  | VRuntime (PacketOut(p0,p1)) -> Cstruct.append p0 p1
  | _ -> failwith "pack not a packet"

and eval_ebpf_ctrl (control : value) (args : Argument.t list) 
    (env : EvalEnv.t) : EvalEnv.t * signal =
  let (env,s,_) = eval_app env SContinue control args in 
  (env,s) 

and eval_v1control (control : value) (args : Argument.t list)
    (env : EvalEnv.t) : EvalEnv.t * signal =
  let (env,s,_) = eval_app env SContinue control args in
  (env,s)

(*----------------------------------------------------------------------------*)
(* Program Evaluation *)
(*----------------------------------------------------------------------------*)

let eval_expression env expr =
  let (a,b,c) = eval_expression' env SContinue expr in
  (a,c)

let hex_of_nibble (i : int) : string =
  match i with
  | 0 -> "0"
  | 1 -> "1"
  | 2 -> "2"
  | 3 -> "3"
  | 4 -> "4"
  | 5 -> "5"
  | 6 -> "6"
  | 7 -> "7"
  | 8 -> "8"
  | 9 -> "9"
  | 10 -> "A"
  | 11 -> "B"
  | 12 -> "C"
  | 13 -> "D"
  | 14 -> "E"
  | 15 -> "F"
  | _ -> failwith "unreachable"

let hex_of_int (i : int) : string =
  hex_of_nibble (i/16) ^ hex_of_nibble (i%16) ^ " "

let hex_of_char (c : char) : string =
  c |> Char.to_int |> hex_of_int

let hex_of_string (s : string) : string =
  s
  |> String.to_list
  |> List.map ~f:hex_of_char
  |> List.fold_left ~init:"" ~f:(^)

let eval_program (p : Types.program) (pack : packet_in)
  (ctrl : Table.pre_entry list) : unit =
  match p with Program l ->
    let env = List.fold_left l ~init:EvalEnv.empty_eval_env ~f:eval_decl in
    EvalEnv.print_env env;
    Format.printf "Done\n";
    let packetout = eval_main env pack ctrl in
    print_string "Resulting packet: ";
    packetout
    |> Cstruct.to_string
    |> hex_of_string
    |> print_endline
