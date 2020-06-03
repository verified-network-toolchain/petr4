module I = Info
open Core_kernel
open Env
open Prog
open Typed
open Value
open Target
open Bitstring
open Util
module Info = I (* JNF: ugly hack *)
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)
let (>>|) v f = Option.map ~f:f v

type env = EvalEnv.t

module type Interpreter = sig
  
  type state
  
  val empty_state : state

  val eval : ctrl -> env -> state -> pkt -> Bigint.t -> state * env * pkt option

  val eval_prog : ctrl -> env -> state -> buf -> Bigint.t -> program -> 
    state * (buf * Bigint.t) option

  val eval_decl : ctrl -> env -> state -> Declaration.t -> (env * state)

  val eval_statement : ctrl -> env -> state -> Statement.t -> (env * state)

  val eval_expression : ctrl -> env -> state  -> Expression.t -> (env * state * value)

  val eval_app : ctrl -> env -> state -> signal -> value -> Expression.t option list -> env * state * signal * value

end

module MakeInterpreter (T : Target) = struct 

  type state = T.state

  let empty_state = State.empty

  let assign_lvalue = assign_lvalue T.read_header_field T.write_header_field

  let value_of_lvalue = value_of_lvalue T.read_header_field

  (*----------------------------------------------------------------------------*)
  (* Declaration Evaluation *)
  (*----------------------------------------------------------------------------*)

  let rec eval_decl (ctrl : ctrl) (env : env) (st : state) 
      (d : Declaration.t) : env * state =
    match snd d with
    | Constant {
        annotations = _;
        typ = t;
        value = v;
        name = (_,n);
      } -> eval_const_decl ctrl env st t v n
    | Instantiation {
        annotations = _;
        typ = typ;
        args = args;
        name = (_,n);
        init = None
      } -> eval_instantiation ctrl env st typ args n
    | Instantiation { init = Some _; _ } ->
      failwith "evaluating instantiations with initializers is unimplemented"
    | Parser {
        annotations = _;
        name = (_,n);
        type_params = _;
        params = _;
        constructor_params = _;
        locals = _;
        states = _;
      } -> (eval_parser_decl env n d, st)
    | Control {
        annotations = _;
        name = (_,n);
        type_params = _;
        params = _;
        constructor_params = _;
        locals = _;
        apply = _;
      } -> (eval_control_decl env n d, st)
    | Function {
        return = _;
        name = (_,n);
        type_params = _;
        params = ps;
        body = b;
      } -> (eval_fun_decl env n ps b d, st)
    | ExternFunction {
        annotations = _;
        return = _;
        name = (_,n);
        type_params = _;
        params = ps;
      } -> (eval_extern_fun env n ps d, st)
    | Variable {
        annotations = _;
        typ = t;
        name = (_,n);
        init = v;
      } -> let (a,b,_) = eval_var_decl ctrl env st t n v in (a,b)
    | ValueSet {
        annotations = _;
        typ = t;
        size = s;
        name = (_,n);
      } -> let (a,b,_) = eval_set_decl ctrl env st t n s in (a,b)
    | Action {
        annotations = _;
        name = (_,n);
        data_params;
        ctrl_params;
        body = b;
      } -> (eval_action_decl env n data_params ctrl_params b d, st)
    | Table {
        annotations = _;
        name = (_,n);
        key;
        actions;
        entries;
        default_action;
        size;
        custom_properties = ps;
      } -> (eval_table_decl ctrl env st n d key actions entries default_action size ps)
    | Header {
        annotations = _;
        name = (_,n);
        fields = _;
      } -> (eval_header_decl env n d, st)
    | HeaderUnion {
        annotations = _;
        name = (_,n);
        fields = _;
      } -> (eval_union_decl env n d, st)
    | Struct {
        annotations = _;
        name = (_,n);
        fields = _;
      } -> (eval_struct_decl env n d, st)
    | Error {
        members = l;
      } -> (eval_error_decl env l, st)
    | MatchKind {
        members = _;
      } -> (eval_matchkind_decl env d, st)
    | Enum {
        annotations = _;
        name = (_,n);
        members = _;
      } -> (eval_enum_decl env n d, st)
    | SerializableEnum {
        annotations = _;
        typ = _;
        name = (_,n);
        members = _;
      } -> (eval_senum_decl env n d, st)
    | ExternObject {
        annotations = _;
        name = (_,n);
        type_params = tps;
        methods = ms;
      } -> (eval_extern_obj env n ms d, st)
    | TypeDef {
        annotations = _;
        name = (_,n);
        typ_or_decl = _;
      } -> (eval_type_def env n d, st)
    | NewType {
        annotations = _;
        name = (_,n);
        typ_or_decl = _;
      } -> (eval_type_decl env n d, st)
    | ControlType {
        annotations = _;
        name = (_,n);
        type_params = _;
        params = _;
      } -> (eval_ctrltyp_decl env n d, st)
    | ParserType {
        annotations = _;
        name = (_,n);
        type_params = _;
        params = _;
      } -> (eval_prsrtyp_decl env n d, st)
    | PackageType {
        annotations = _;
        name = (_,n);
        type_params = _;
        params = _;
      } -> (eval_pkgtyp_decl env n d, st)

  and eval_const_decl (ctrl : ctrl) (env : env) (st : state) (typ : Type.t) (v : value)
      (name : string) : env * state =
    let v = implicit_cast env v typ in
    EvalEnv.insert_val_bare name v env, st

  and eval_instantiation (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (args : Expression.t list) (name : string) : env * state =
    let env' = EvalEnv.set_namespace (EvalEnv.get_namespace env ^ name) env in
    let (env',st',_,obj) = eval_nameless ctrl env' st typ args in
    let env' = EvalEnv.set_namespace (EvalEnv.get_namespace env) env' in
    (EvalEnv.insert_val_bare name obj env', st')

  and eval_parser_decl (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_control_decl (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_fun_decl (env : env) (name : string) (params : TypeParameter.t list)
      (body : Block.t) (decl : Declaration.t) : env =
    EvalEnv.insert_val_bare name (VFun{params;body}) env
    |> EvalEnv.insert_decl_bare name decl

  and eval_extern_fun (env : env) (name : string)
      (params : TypeParameter.t list) (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env
    |> EvalEnv.insert_val_bare name (VExternFun {name; caller = None})

  and eval_var_decl (ctrl : ctrl) (env : env) (st : state) (typ : Type.t) (name : string)
      (init : Expression.t option) : env * state * signal =
    match init with
    | None ->
      let init_val = init_val_of_typ env typ in
      let env = EvalEnv.insert_val_bare name init_val env in
      env, st, SContinue
    | Some e ->
      let env, st, signal, init_val = eval_expr ctrl env st SContinue e in
      match signal with
      | SContinue ->
         let init_val = implicit_cast env init_val typ in
         let env = EvalEnv.insert_val_bare name init_val env in
         env, st, SContinue
      | signal -> env, st, signal

  and eval_set_decl (ctrl : ctrl) (env : env) (st : state) (typ : Type.t) (name : string)
      (size : Expression.t) : env * state * signal =
    let env' = EvalEnv.insert_typ_bare name typ env in
    let (env'', st', s, size') = eval_expr ctrl env' st SContinue size in
    let size'' = assert_rawint size' in
    match s with
    | SContinue ->
      let ms = snd ctrl in
      if Bigint.(Bigint.of_int (List.length ms) > size'')
      then failwith "too many elements inserted to value set"
      else
      let vset = VSet (SValueSet{size=size';members=ms;sets=[]}) in
      let env''' = EvalEnv.insert_val_bare name vset env'' in
      (env''', st', s)
    | SReject _ -> (env, st', s)
    | _ -> failwith "value set declaration should not return or exit"

  and eval_action_decl (env : env) (name : string) (data_params : TypeParameter.t list)
      (ctrl_params : TypeParameter.t list) (body : Block.t)
      (decl : Declaration.t) : env  =
    EvalEnv.insert_val_bare name (VAction{params = data_params @ ctrl_params; body}) env
    |> EvalEnv.insert_decl_bare name decl

  and eval_table_decl (ctrl : ctrl) (env : env) (st : state) (name : string)
      (decl : Declaration.t) (key : Table.key list) (actions : Table.action_ref list)
      (entries : (Table.entry list) option) (default : Table.action_ref option)
      (size : P4Int.t option) (props : Table.property list) : env * state =
    let env' = EvalEnv.insert_decl_bare name decl env in
    let ctrl_entries = fst ctrl in
    let pre_ks = key |> List.map ~f:snd in
    let final_entries = match entries with
                        | None -> ctrl_entries
                        | Some entries -> entries |> List.map ~f:snd in
    let v = VTable { name = name;
                    keys = pre_ks;
                    actions = actions;
                    default_action = default_of_defaults default;
                    const_entries = final_entries; } in
    (EvalEnv.insert_val_bare name v env', st)

  and eval_header_decl (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_union_decl (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_struct_decl (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_error_decl (env : env) (errs : P4String.t list) : env =
    env

  and eval_matchkind_decl (env : env) (d : Declaration.t) : env =
    env

  and eval_enum_decl (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_senum_decl (env : env) (name : string)
      (decl : Declaration.t) :env =
    EvalEnv.insert_decl_bare name decl env

  and eval_extern_obj (env : env) (name : string)
      (methods : MethodPrototype.t list) (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_type_def (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_type_decl (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_ctrltyp_decl (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_prsrtyp_decl (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

  and eval_pkgtyp_decl (env : env) (name : string)
      (decl : Declaration.t) : env =
    EvalEnv.insert_decl_bare name decl env

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
  
  (*----------------------------------------------------------------------------*)
  (* Statement Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_stmt (ctrl : ctrl) (env : env) (st : state) (sign : signal)
      (stm : Statement.t) : (env * state * signal) =
    match (snd stm).stmt with
    | MethodCall{func;type_args=ts;args} -> eval_method_call ctrl env st sign func ts args
    | Assignment{lhs;rhs}                -> eval_assign ctrl env st sign lhs rhs
    | DirectApplication{typ;args}        -> eval_app' ctrl env st sign args typ
    | Conditional{cond;tru;fls}          -> eval_cond ctrl env st sign cond tru fls
    | BlockStatement{block}              -> eval_block ctrl env st sign block
    | Exit                               -> eval_exit env st sign
    | EmptyStatement                     -> (env, st, sign)
    | Return{expr}                       -> eval_return ctrl env st sign expr
    | Switch{expr;cases}                 -> eval_switch ctrl env st sign expr cases
    | DeclarationStatement{decl}         -> eval_decl_stm ctrl env st sign decl

  and eval_method_call (ctrl : ctrl) (env : env) (st : state) (sign : signal)
      (func : Expression.t) (targs : Type.t list)
      (args : Expression.t option list) : env * state * signal =
    match sign with
    | SContinue -> let (e,s,i,_) = eval_funcall ctrl env st func targs args in (e,s,i)
    | SReject _
    | SReturn _
    | SExit     -> (env, st, sign)

  and eval_assign (ctrl : ctrl) (env : env) (st : state) (s : signal) (lhs : Expression.t)
      (rhs : Expression.t) : env * state * signal =
    match s with
    | SContinue ->
      let (env', st', s', v) = eval_expr ctrl env st SContinue rhs in
      let (env'', st'', s'', lv) = lvalue_of_expr ctrl env st s lhs in
      begin match s',s'', lv with
        | SContinue, SContinue, Some lv -> let (env, s) = assign_lvalue env' lv v false in env, st', s
        | SContinue, _, _               -> env'', st'', s''
        | _, _, _                       -> (env', st', s')
      end
    | SReject _
    | SReturn _
    | SExit     -> (env, st, s)

  and eval_app (ctrl : ctrl) (env : env) (st : state) (s : signal) (v : value)
    (args : Expression.t option list) : env * state * signal * value =
    match s with
    | SContinue ->
      begin match v with
        | VParser {pvs;pparams;plocals;states} ->
          let (env, s, st') = eval_parser ctrl env st pparams args pvs plocals states in
          (env,s, st', VNull)
        | VControl {cvs;cparams;clocals;apply} ->
          let (env,st,s) = eval_control ctrl env st cparams args cvs clocals apply in
          (env,st,s,VNull)
        | VTable {keys;const_entries;name;actions;default_action} ->
          eval_table ctrl env st keys const_entries name actions default_action
        | _ -> failwith "apply not implemented on type" end
    | SReject _
    | SReturn _
    | SExit -> (env, st, s, VNull)

  and name_only name =
    match name with
    | Types.BareName s
    | Types.QualifiedName (_, s) ->
       snd s

  and eval_table (ctrl : ctrl) (env : env) (st : state) (key : Table.pre_key list)
      (entries : Table.pre_entry list)
      (name : string) (actions : Table.action_ref list)
      (default : Table.action_ref) : env * state * signal * value =
    let ks = key |> List.map ~f:(fun k -> k.key) in
    let mks = key |> List.map ~f:(fun k -> k.match_kind |> snd) in
    let ((env',st',s), ks') = List.fold_map ks ~init:(env, st, SContinue)
        ~f:(fun (a, b, c) k ->
            let w,x,y,z = eval_expr ctrl a b c k in ((w,x,y),z)) in
    let f ((v,w,x,y),z) = ((v,w,x),(y,z)) in
    let sort_mks = check_lpm_count mks in
    let ws = List.map ks' ~f:width_of_val in
    let ((env'', st'', s'),entries') =
      List.fold_map entries ~init:(env',st',s)
        ~f:(fun (a,b,c) d -> (set_of_matches ctrl a b c d.matches ws, d.action) |> f) in
    let (entries'', ks'') = if List.equal String.equal mks ["lpm"] then (sort_lpm entries', ks')
      else if sort_mks then filter_lpm_prod env'' mks ks' entries'
      else (entries', ks') in
    let l = List.filter entries'' ~f:(fun (s,a) -> values_match_set ks'' s) in
    let action = match l with
                | [] -> default
                | _ -> List.hd_exn l |> snd in
    let action_name = Table.((snd action).action.name) in
    let action_value = EvalEnv.find_val action_name env in
    let args = Table.((snd action).action.args) in
    match action_value with
    | VAction{params;body}  ->
      let (env',st',s,_) = eval_funcall' ctrl env'' st'' params args body in
      let v = VStruct {fields=[
                            ("hit", VBool (not (List.is_empty l)));
                            ("miss", VBool (List.is_empty l));
                            ("action_run", VEnumField{typ_name=name;
                                                      enum_name=name_only action_name})
                          ]} in
      (env',st',s,v)
    | _ -> failwith "table expects an action"

  (* TODO: double check about scoping - actions before tables? *)

  and filter_lpm_prod (env : env) (mks : string list) (ks : value list)
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
      |> List.filter ~f:(fun (s,a) -> values_match_set ks s)
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
    | SUniversal
    | SLpm _ -> s
    | SRange _
    | SValueSet _ -> failwith "unreachable"

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
    let (env', st', sign', v) = eval_nameless ctrl env st t  [] in
    let typname = name_only (name_of_type_ref t) in 
    let args' = List.map ~f:(fun arg -> Some arg) args in
    let env'' = EvalEnv.set_namespace (EvalEnv.get_namespace env' ^ typname) env' in
    let (env'', st'', sign'', _) = eval_app ctrl env'' st' sign' v args' in
    (EvalEnv.set_namespace (EvalEnv.get_namespace env') env'', st'', sign'')

  and eval_cond (ctrl : ctrl) (env : env) (st : state) (sign : signal) (cond : Expression.t)
      (tru : Statement.t) (fls : Statement.t option) : env * state * signal =
    let eval_cond' env cond tru fls =
      let (env', st', s', v) = eval_expr ctrl env st SContinue cond in
      match s' with
      | SReject _ -> (env', st', s')
      | SContinue ->
        begin match v with
          | VBool true  -> eval_stmt ctrl env' st' SContinue tru
          | VBool false ->
            begin match fls with
              | None -> (env, st, SContinue)
              | Some fls' -> eval_stmt ctrl env' st' SContinue fls'  end
          | _ -> failwith "conditional guard must be a bool" end
      | _ -> failwith "unreachable" in
    match sign with
    | SContinue -> eval_cond' env cond tru fls
    | SReject _
    | SReturn _
    | SExit     -> (env, st, sign)

  and eval_block (ctrl : ctrl) (env : env) (st : state) (sign :signal) 
      (block : Block.t) : (env * state * signal) =
    let block = snd block in
    let f (env,st,sign) stm =
      match sign with
      | SContinue -> eval_stmt ctrl env st sign stm
      | SReject _
      | SReturn _
      | SExit     -> (env, st, sign) in
    List.fold_left block.statements ~init:(env,st,sign) ~f:f

  and eval_exit (env : env) (st : state) (sign : signal) : (env * state * signal) =
      match sign with 
      | SContinue -> (env, st, SExit)
      | SReturn v -> (env, st, SReturn v) 
      | SExit -> (env, st, SExit)
      | SReject _ -> failwith "reject and exit in the same block"

  and eval_return (ctrl : ctrl) (env : env) (st : state) (sign : signal)
      (expr : Expression.t option) : (env * state * signal) =
    let (env', st', s', v) =
      match expr with
      | None   -> (env, st, SContinue, VNull)
      | Some e -> eval_expr ctrl env st SContinue e in
    match sign with
    | SReject _
    | SReturn _
    | SExit -> (env,st,sign)
    | SContinue -> begin match s' with
        | SContinue -> (env', st', SReturn v)
        | SReject _ -> (env', st', s')
        | SReturn _
        | SExit     -> failwith "unreachable" end

  and eval_switch (ctrl : ctrl) (env : env) (st : state) (sign : signal) (expr : Expression.t)
      (cases : Statement.switch_case list) : env * state * signal = 
    let open Statement in 
    let (env',st',s',v) = eval_expr ctrl env st SContinue expr in 
    match sign with 
    | SReject _
    | SReturn _ 
    | SExit -> (env, st, sign)
    | SContinue -> begin match s' with 
      | SReject _ -> (env', st', s') 
      | SContinue -> 
        let s = assert_enum v |> snd in 
        let matches = cases 
                      |> List.map ~f:snd
                      |> List.group ~break:(fun x _ -> match x with Action _ -> true | _ -> false)
                      |> List.filter ~f:(fun l -> List.exists l ~f:(label_matches_string s)) in
        begin match matches with
              | [] -> (env', st', s')
              | hd::tl -> hd
                        |> List.filter ~f:(function Action _ -> true | _ -> false) 
                        |> List.hd_exn 
                        |> (function Action{label;code} -> code | _ -> failwith "unreachable")
                        |> eval_block ctrl env' st' SContinue end
      | _ -> failwith "unreachable" end

  and eval_decl_stm (ctrl : ctrl) (env : env) (st : state) (sign : signal)
(decl : Declaration.t) : env * state * signal =
    match sign with
    | SReject _
    | SReturn _
    | SExit     -> (env, st, sign)
    | SContinue -> 
       let (env', st') = eval_decl ctrl env st decl in 
       (env', st', SContinue)

  (*----------------------------------------------------------------------------*)
  (* Functions on L-Values*)
  (*----------------------------------------------------------------------------*)

  and lvalue_of_expr (ctrl : ctrl) (env : env) (st : state) (signal : signal)
      (expr : Expression.t) : env * state * signal * lvalue option =
    match signal with
    | SContinue -> begin match (snd expr).expr with
      | Name name -> env, st, SContinue, Some {lvalue = LName {name}; typ = (snd expr).typ}
      | ExpressionMember{expr=e; name=(_,n)} -> lvalue_of_expr_mem ctrl env st (snd expr).typ e n
      | BitStringAccess{bits;lo;hi} -> lvalue_of_expr_bsa ctrl env st (snd expr).typ bits lo hi
      | ArrayAccess{array=a;index} -> lvalue_of_expr_ara ctrl env st (snd expr).typ a index
      | _ -> failwith "not an lvalue" end
    | SReject _ | SExit | SReturn _ -> env, st, signal, None

  and lvalue_of_expr_mem (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (e : Expression.t) (n : string) : env * state * signal * lvalue option =
    let (env', st', signal, lv) = lvalue_of_expr ctrl env st SContinue e in
    env', st', signal, 
    lv >>| fun lv -> {lvalue = LMember {expr = lv; name = n}; typ }

  and lvalue_of_expr_bsa (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (n : Expression.t) (lsb : Bigint.t)
      (msb : Bigint.t) : env * state * signal * lvalue option =
    let (env', st', signal, lv) = lvalue_of_expr ctrl env st SContinue n in
    match signal with
    | SReject _ | SExit | SReturn _ -> env', st', signal, lv
    | SContinue ->
      env', st', signal,
      lv >>| fun lv -> {lvalue = LBitAccess{expr=lv; msb = msb; lsb = lsb}; typ}   

  and lvalue_of_expr_ara (ctrl : ctrl) (env : env) (st : state) (typ : Type.t) 
      (a : Expression.t) (idx : Expression.t) : env * state * signal * lvalue option =
    let (env', st', s, lv) = lvalue_of_expr ctrl env st SContinue a in
    let (env'', st'', s', idx') = eval_expr ctrl env st SContinue idx in
    match s, s' with
    | SContinue, SContinue -> 
      env'', st'', s',
      lv >>| fun lv -> {lvalue = LArrayAccess{expr=lv; idx=idx'}; typ }
    | SContinue, _ -> env'', st'', s', lv
    | _, _ -> env', st', s, lv

  (*----------------------------------------------------------------------------*)
  (* Expression Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_expr (ctrl : ctrl) (env : env) (st : state) (s : signal)
      (exp : Expression.t) : env * state * signal * value =
    match s with
    | SContinue ->
      begin match (snd exp).expr with
        | True                            -> (env, st, s, VBool true)
        | False                           -> (env, st, s, VBool false)
        | Int(_,n)                        -> (env, st, s, eval_p4int n)
        | String (_,value)                -> (env, st, s, VString value)
        | Name name                       -> eval_name ctrl env st s name exp
        | ArrayAccess{array=a; index=i}   -> eval_array_access ctrl env st a i
        | BitStringAccess({bits;lo;hi})   -> eval_bitstring_access ctrl env st bits hi lo
        | Record{entries}                 -> eval_record ctrl env st entries
        | List{values}                    -> eval_list ctrl env st values
        | UnaryOp{op;arg}                 -> eval_unary ctrl env st op arg
        | BinaryOp{op; args=(l,r)}        -> eval_binop ctrl env st op l r
        | Cast{typ;expr}                  -> eval_cast ctrl env st typ expr
        | TypeMember{typ;name}            -> eval_typ_mem ctrl env st typ (snd name)
        | ErrorMember t                   -> (env, st, s, VError (snd t))
        | ExpressionMember{expr;name}     -> eval_expr_mem ctrl env st expr name
        | Ternary{cond;tru;fls}           -> eval_ternary ctrl env st cond tru fls
        | FunctionCall{func;args;type_args=targs}       -> eval_funcall ctrl env st func targs args
        | NamelessInstantiation{typ;args} -> eval_nameless ctrl env st typ args
        | Mask{expr;mask}                 -> eval_mask ctrl env st expr mask
        | Range{lo;hi}                    -> eval_range ctrl env st lo hi
        | DontCare                        -> env, st, s, VNull end
    | SReject _ -> (env, st, s, VNull)
    | SReturn _ -> failwith "expression should not return"
    | SExit -> failwith "expresion should not exit"

  and eval_name (ctrl : ctrl) (env : env) (st : state) (s : signal) (name : Types.name)
      (exp : Expression.t) : env * state * signal * value =
    if String.equal (name_only name) "verify"
    then (env, st, s, VExternFun {name = "verify"; caller = None})
    else (env, st, s, EvalEnv.find_val name env)

  and eval_p4int (n : P4Int.pre_t) : value =
    match n.width_signed with
    | None          -> VInteger n.value
    | Some(w,true)  -> VInt {w=Bigint.of_int w;v=n.value}
    | Some(w,false) -> VBit {w=Bigint.of_int w;v=n.value}

  and eval_array_access (ctrl : ctrl) (env : env) (st : state) (a : Expression.t)
      (i : Expression.t) : env * state * signal * value =
    let (env', st', s, a') = eval_expr ctrl env st SContinue a in
    let (env'', st'', s', i') = eval_expr ctrl env' st' SContinue i in
    let idx = bigint_of_val i' in
    let (hdrs,size,next) = assert_stack a' in
    let idx' = Bigint.(to_int_exn (idx % size)) in
    match (s,s') with
    | SContinue, SContinue -> (env'', st'', SContinue, List.nth_exn hdrs idx')
    | SReject _,_ -> (env',st',s, VNull)
    | _,SReject _ -> (env'',st'',s',VNull)
    | _ -> failwith "unreachable"

  and eval_bitstring_access (ctrl : ctrl) (env : env) (st : state) (b : Expression.t)
      (m : Bigint.t) (l : Bigint.t) : env * state * signal * value =
    let (env', st', s, b) = eval_expr ctrl env st SContinue b in
    let b' = bigint_of_val b in
    let w = Bigint.(m-l + one) in
    let n = bitstring_slice b' m l in
    match s with
    | SContinue -> (env', st', SContinue, VBit{w;v=n})
    | SReject _ | SExit | SReturn _ -> (env',st',s,VNull)

  and eval_record (ctrl : ctrl) (env : env) (st : state) (kvs : KeyValue.t list) : env * state * signal * value =
    let es = List.map kvs ~f:(fun kv -> (snd kv).value) in
    let ks = List.map kvs ~f:(fun kv -> snd (snd kv).key) in
    let f (a,b,c) d =
      let (w,x,y,z) = eval_expr ctrl a b c d in
      ((w,x,y),z) in
    es
    |> List.fold_map ~f:f ~init:(env, st, SContinue)
    |> (fun ((e,st,s),l) -> e,st,s, VRecord (List.zip_exn ks l))
  
  and eval_list (ctrl : ctrl) (env : env) (st : state) 
      (values : Expression.t list) : env * state * signal * value =
    let f (a,b,c) d =
      let (w,x,y,z) = eval_expr ctrl a b c d in
      ((w,x,y),z) in
    values
    |> List.fold_map ~f:f ~init:(env,st,SContinue)
    |> (fun ((e,st,s),l) -> (e, st, s, VTuple l))

  and eval_unary (ctrl : ctrl) (env : env) (st : state) (op : Op.uni)
      (e : Expression.t) : env * state * signal * value =
    let (env', st', s, v) = eval_expr ctrl env st SContinue e in
    match s with
    | SContinue ->
       let v = Ops.interp_unary_op op v in
      (env,st', s,v)
    | SReject _ -> (env',st',s,VNull)
    | _ -> failwith "unreachable"

  and eval_binop (ctrl : ctrl) (env : env) (st : state) (op : Op.bin) (l : Expression.t)
      (r : Expression.t) : env * state * signal * value =
    let (env',st',s,l) = eval_expr ctrl env st SContinue l in
    let (env'',st'',s',r) = eval_expr ctrl env' st' SContinue r in
    let v = Ops.interp_binary_op op l r in
    match (s,s') with
    | SContinue, SContinue -> (env'', st'', SContinue, v)
    | SReject _,_ -> (env',st',s,VNull)
    | _,SReject _ -> (env'',st'',s',VNull)
    | _ -> failwith "unreachable"

  and eval_cast (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (expr : Expression.t) : env * state * signal * value =
    let (env', st', s, v) = eval_expr ctrl env st SContinue expr in
    let v' = Ops.interp_cast typ v
               ~type_lookup:(fun name -> EvalEnv.find_typ name env)
    in
    match s with
    | SContinue -> (env',st',s,v')
    | _ -> (env',st',s,VNull)

  and eval_typ_mem (ctrl : ctrl) (env : env) (st : state) (typ : Types.name)
      (name : string) : env * state * signal * value =
    match EvalEnv.find_decl typ env with
    | info, Declaration.Enum {members=ms;name=(_,n);_} ->
       let mems = List.map ms ~f:snd in
       if List.mem mems name ~equal:String.equal
       then (env, st, SContinue, VEnumField{typ_name=n;enum_name=name})
       else raise (UnboundName name)
    | info, Declaration.SerializableEnum {members=ms;name=(_,n);typ;_ } ->
       let ms' = List.map ms ~f:(fun (a,b) -> (snd a, b)) in
       let expr = find_exn ms' name in
       let (env',st',s,v) = eval_expr ctrl env st SContinue expr in
       let v' = implicit_cast_from_rawint env' v typ in
       begin match s with
       | SContinue -> (env',st',s,VSenumField{typ_name=n;enum_name=name;v=v'})
       | SReject _ -> (env',st',s,VNull)
       | _ -> failwith "unreachable" end
    | _ -> failwith "typ mem undefined"

  and eval_expr_mem (ctrl : ctrl) (env : env) (st : state) (expr : Expression.t)
      (name : P4String.t) : env * state * signal * value =
    let (env', st', s, v) = eval_expr ctrl env st SContinue expr in
    let fourth4 (_,_,_,x) = x in
    match s with
    | SContinue ->
      begin match v with
        | VTuple _ -> failwith "tuple member does not exist"
        | VNull
        | VBool _
        | VInteger _
        | VBit _
        | VInt _
        | VVarbit _
        | VSet _
        | VString _
        | VError _
        | VMatchKind _
        | VFun _
        | VBuiltinFun _
        | VAction _
        | VEnumField _
        | VSenumField _
        | VExternFun _
        | VPackage _                         -> failwith "expr member does not exist"
        | VStruct{fields=fs}                 -> eval_struct_mem env' st' (snd name) fs
        | VHeader{fields=fs;is_valid=vbit}   -> eval_header_mem ctrl env' st' (snd name) expr fs vbit
        | VUnion{fields=fs}                  -> eval_union_mem ctrl env' st' (snd name) expr fs
        | VStack{headers=hdrs;size=s;next=n} -> eval_stack_mem ctrl env' st' (snd name) expr hdrs s n
        | VRuntime {loc; obj_name}           -> eval_runtime_mem env' st' (snd name) expr loc obj_name
        | VRecord fs                         -> env', st', s, find_exn fs (snd name)
        | VParser _
        | VControl _ -> 
          env', st', s,
          VBuiltinFun {
            name = snd name;
            caller = lvalue_of_expr ctrl env st SContinue expr |> fourth4 |> Option.value_exn }
        | VTable _ -> 
          env', st', s,
          VBuiltinFun {
            name = snd name;
            caller = lvalue_of_expr ctrl env st SContinue expr |> fourth4 |> Option.value_exn } end
    | SReject _ -> (env',st',s,VNull)
    | _ -> failwith "unreachable"

  and eval_ternary (ctrl : ctrl) (env : env) (st : state) (c : Expression.t)
      (te : Expression.t) (fe : Expression.t) : env * state * signal * value =
    let (env', st', s, c') = eval_expr ctrl env st SContinue c in
    match c' with
    | VBool(true)  -> (eval_expr ctrl env' st' s te)
    | VBool(false) -> (eval_expr ctrl env' st' s fe)
    | _ -> failwith "ternary guard must be a bool"

  and eval_funcall (ctrl : ctrl) (env : env) (st : state) (func : Expression.t)
      (targs : Type.t list)
      (args : Expression.t option list) : env * state * signal * value =
    let (env', st', s, cl) = eval_expr ctrl env st SContinue func in
    match s with
    | SContinue ->
      begin match cl with
        | VAction{params; body}
        | VFun{params; body}            -> eval_funcall' ctrl env' st' params args body
        | VBuiltinFun{name=n;caller=lv} -> eval_builtin ctrl env' st' n lv args
        | VExternFun{name=n;caller=v}   -> eval_extern_call ctrl env' st' n v targs args
        | _ -> failwith "unreachable" end
    | SReject _ -> (env',st',s,VNull)
    | _ -> failwith "unreachable"

  and name_of_type_ref (typ: Type.t) =
    match typ with
    | TypeName name -> name
    | NewType nt -> BareName (Info.dummy, nt.name)
    | Enum et -> BareName (Info.dummy, et.name)
    | SpecializedType { base; args = _ } ->
       name_of_type_ref base
    | _ -> failwith "can't find name for this type"

  and eval_nameless (ctrl : ctrl) (env : env) (st : state) (typ : Type.t)
      (args : Expression.t list) : env * state * signal * value =
    let name = name_of_type_ref typ in
    let decl = EvalEnv.find_decl name env in
    let args' = List.map ~f:(fun arg -> Some arg) args in
    let (env',st',s,v) = let open Declaration in match snd decl with
      | Control typ_decl ->
        let (env',st',s) = copyin ctrl env st typ_decl.constructor_params args' in
        let state = env' |> EvalEnv.get_val_firstlevel |> List.rev in
        let v' = VControl { cvs = state;
                            cparams = typ_decl.params;
                            clocals = typ_decl.locals;
                            apply = typ_decl.apply; } in
        (EvalEnv.pop_scope env',st',s,v')
      | Parser typ_decl ->
        let (env',st',s) = copyin ctrl env st typ_decl.constructor_params args' in
        let state = env' |> EvalEnv.get_val_firstlevel |> List.rev in
        let v' = VParser { pvs = state;
                          pparams = typ_decl.params;
                          plocals = typ_decl.locals;
                          states = typ_decl.states; } in
        (EvalEnv.pop_scope env',st',s,v')
      | PackageType pack_decl ->
        let (env',st',s) = copyin ctrl env st pack_decl.params args' in
        let state = env' |> EvalEnv.get_val_firstlevel |> List.rev in
        (EvalEnv.pop_scope env', st', s, VPackage{decl;args=state})
      | ExternObject ext_decl -> 
        let loc = EvalEnv.get_namespace env in
        if State.is_initialized loc st
        then env, st, SContinue, VRuntime {loc = loc; obj_name = (snd ext_decl.name);}
        else 
          let args' = List.map args ~f:(fun x -> Some x) in
          eval_extern_call ctrl env st (snd ext_decl.name) (Some (loc, snd ext_decl.name)) [] args'  
      | _ -> failwith "instantiation unimplemented" in
    match s with
    | SContinue -> (env',st',s,v)
    | SReject _ -> (env,st',s,VNull)
    | _ -> failwith "nameless should not return or exit"

  and eval_mask (ctrl : ctrl) (env : env) (st : state) (e : Expression.t)
      (m : Expression.t) : env * state * signal * value =
    let (env', st', s, v1)  = eval_expr ctrl env st SContinue e in
    let (env'', st'', s', v2) = eval_expr ctrl env' st SContinue m in
    match (s,s') with
    | SContinue, SContinue -> (env'', st'', s, VSet(SMask{v=v1;mask=v2}))
    | SReject _,_ -> (env',st',s,VNull)
    | _,SReject _ -> (env'',st'',s',VNull)
    | _ -> failwith "unreachable"

  and eval_range (ctrl : ctrl) (env : env) (st : state) (lo : Expression.t)
      (hi : Expression.t) : env * state * signal * value =
    let (env', st',s, v1)  = eval_expr ctrl env st SContinue lo in
    let (env'', st'',s', v2) = eval_expr ctrl env' st SContinue hi in
    match (s,s') with
    | SContinue, SContinue -> (env'', st'', s, VSet(SRange{lo=v1;hi=v2}))
    | SReject _,_ -> (env',st',s,VNull)
    | _,SReject _ -> (env'',st'',s',VNull)
    | _ -> failwith "unreachable"

  (*----------------------------------------------------------------------------*)
  (* Membership Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_struct_mem (env : env) (st : state) (name : string)
      (fs : (string * value) list) : env * state * signal * value =
    (env, st, SContinue, find_exn fs name)

  and eval_header_mem (ctrl : ctrl) (env : env) (st : state) (fname : string)
      (e : Expression.t) (fs : (string * value) list)
      (valid : bool) : env * state * signal * value =
    let (env', st', signal, lv) = lvalue_of_expr ctrl env st SContinue e in
    match fname with
    | "isValid"
    | "setValid"
    | "setInvalid" -> 
      begin match signal, lv with
        | SContinue, Some lv -> env', st', SContinue, VBuiltinFun{name=fname;caller=lv}
        | _, _ -> env', st', signal, VNull end
    | _ -> (env, st, SContinue, T.read_header_field valid fs fname)

  and eval_union_mem (ctrl : ctrl) (env : env) (st : state)
    (fname : string) (e : Expression.t) (fs : (string * value) list)
    : env * state * signal * value =
    let (env', st', signal, lv) = lvalue_of_expr ctrl env st SContinue e in
    match fname with
    | "isValid" ->
       begin match signal, lv with
       | SContinue, Some lv -> env', st', SContinue, VBuiltinFun{name=fname;caller=lv}
       | _, _ -> env', st', signal, VNull end
    | _ -> (env, st, SContinue, find_exn fs fname)

  and eval_stack_mem (ctrl : ctrl) (env : env) (st : state) (fname : string)
      (e : Expression.t) (hdrs : value list) (size : Bigint.t)
      (next : Bigint.t) : env * state * signal * value =
    match fname with
    | "size"       -> eval_stack_size env st size
    | "next"       -> eval_stack_next env st hdrs size next
    | "last"       -> eval_stack_last env st hdrs size next
    | "lastIndex"  -> eval_stack_lastindex env st next
    | "pop_front"
    | "push_front" -> eval_stack_builtin ctrl env st fname e
    | _ -> failwith "stack member unimplemented"

  and eval_runtime_mem (env : env) (st : state) (mname : string) (expr : Expression.t)
      (loc : loc) (obj_name : string) : env * state * signal * value =
    env, st, SContinue, VExternFun {caller = Some (loc, obj_name); name = mname }

  and eval_stack_size (env : env) (st : state) 
      (size : Bigint.t) : env * state * signal * value =
    let five = Bigint.(one + one + one + one + one) in
    let thirty_two = shift_bitstring_left Bigint.one five in
    (env, st, SContinue, VBit{w=thirty_two;v=size})

  and eval_stack_next (env : env) (st : state) (hdrs : value list) (size : Bigint.t)
      (next : Bigint.t) : env * state * signal * value =
    let (env', st', s, hdr) =
      if Bigint.(next >= size)
      then (env, st, SReject "StackOutOfBounds", VNull)
      else (env, st, SContinue, List.nth_exn hdrs Bigint.(to_int_exn next)) in
    (env', st', s, hdr)

  and eval_stack_last (env : env) (st : state) (hdrs : value list) (size : Bigint.t)
      (next : Bigint.t) : env * state * signal *  value =
    let (env', st', s, hdr) =
      if Bigint.(next < one) || Bigint.(next > size)
      then (env, st, SReject "StackOutOfBounds", VNull)
      else (env, st, SContinue, List.nth_exn hdrs Bigint.(to_int_exn (next - one))) in
    (env', st', s, hdr)

  and eval_stack_lastindex (env : env) (st : state) 
      (next : Bigint.t) : env * state * signal * value =
    let five = Bigint.(one + one + one + one + one) in
    let thirty_two = shift_bitstring_left Bigint.one five in
    (env, st, SContinue, VBit{w=thirty_two;v=Bigint.(next - one)})

  and eval_stack_builtin (ctrl : ctrl) (env : env) (st : state) (fname : string)
      (e : Expression.t) : env * state * signal * value =
    let (env', st', signal, lv) = lvalue_of_expr ctrl env st SContinue e in
    env', st', signal, VBuiltinFun{name=fname;caller=lv|>Option.value_exn}

  (*----------------------------------------------------------------------------*)
  (* Function and Method Call Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_extern_call (ctrl : ctrl) (env : env) (st : state) (name : string)
      (v : (loc * string) option) (targs : Type.t list)
      (args : Expression.t option list) : env * state * signal * value =
    let ts = args |> List.map ~f:(function Some e -> (snd e).typ | None -> Void) in
    let params = 
      match v with 
      | Some (_,t) ->
        EvalEnv.find_decl (BareName (Info.dummy, t)) env
        |> assert_extern_obj
        |> List.map ~f:params_of_prototype
        |> List.map ~f:(fun ((_, n), ps) -> (n,ps))
        |> List.filter ~f:(fun (s,_) -> String.equal s name)
        |> List.filter ~f:(fun (_,ps) -> Int.equal (List.length ps) (List.length args))
        |> List.hd_exn
        |> snd
      | None -> EvalEnv.find_decl (BareName (Info.dummy, name)) env
                |> assert_extern_function in
    let fenv = EvalEnv.push_scope env in
    let (_, kvs) =
      List.fold_mapi args ~f:(eval_nth_arg ctrl st params) ~init:(fenv,st,SContinue) in
    let (fenv, st', signal) = copyin ctrl env st params args in
    let vs = List.map ~f:snd kvs in
    let env' = EvalEnv.pop_scope fenv in
    match signal with
    | SExit -> env', st', SExit, VNull
    | SReject s -> env', st', SReject s, VNull
    | SReturn _ | SContinue ->
    let tvs = List.zip_exn vs ts in
    let tvs' = match v with
      | Some (loc, t) -> (VRuntime {loc = loc; obj_name = t;},
                          Type.TypeName (BareName (Info.dummy, "packet"))) :: tvs
      | None -> tvs in
    let (fenv', st'', s, v) = T.eval_extern name ctrl fenv st targs tvs' in
    let inc_next = String.equal name "extract" in (* TODO: violates abstraction *)
    let env'' = copyout ctrl fenv' st'' params args inc_next in
    env'', st'', s, v

  and assert_extern_obj (d : Declaration.t) : MethodPrototype.t list =
    match snd d with 
    | ExternObject x -> x.methods
    | _ -> failwith "expected extern object"

  and params_of_prototype (p : MethodPrototype.t) : P4String.t * TypeParameter.t list =
    match snd p with
    | AbstractMethod x -> (x.name, x.params)
    | Method x -> (x.name, x.params)
    | Constructor x -> (x.name, x.params)

  and assert_extern_function (d : Declaration.t) : TypeParameter.t list =
    match snd d with
    | ExternFunction x -> x.params
    | _ -> failwith "expected extern function"

  and eval_funcall' (ctrl : ctrl) (env : env) (st : state) (params : TypeParameter.t list)
      (args : Expression.t option list) (body : Block.t) : env * state * signal * value =
    let (fenv, st', s) = copyin ctrl env st params args in
    let (fenv', st'', sign) = eval_block ctrl fenv st SContinue body in
    let final_env = copyout ctrl fenv' st'' params args false in
    match sign with
    | SReturn v -> (final_env, st'', SContinue, v)
    | SReject _
    | SContinue
    | SExit     -> (final_env, st'', sign, VNull)

  and copyin (ctrl : ctrl) (env : env) (st : state) (params : TypeParameter.t list)
      (args : Expression.t option list) : env * state * signal =
    let fenv = EvalEnv.push_scope env in
    let ((fenv',st',s),arg_vals) = 
      List.fold_mapi args ~f:(eval_nth_arg ctrl st params) ~init:(fenv,st,SContinue) in
    let fenv' = List.fold2_exn params arg_vals ~init:fenv' ~f:insert_arg in
    match s with
    | SContinue -> (fenv',st',s)
    | SReject _ -> (fenv',st',s)
    | _ -> failwith " unreachable"

  and copyout (ctrl : ctrl) (fenv : env) (st : state) (params : TypeParameter.t list)
      (args : Expression.t option list) (inc_next : bool) : env =
    let env = EvalEnv.pop_scope fenv in
    List.fold2_exn
      params
      args
      ~init:env
      ~f:(copy_arg_out inc_next ctrl st fenv)
    
  and eval_nth_arg (ctrl : ctrl) (st : state) (params : TypeParameter.t list) (i : int) 
      ((env,st,sign) : env * state * signal)
      (e : Expression.t option) : (env * state * signal) * (string * value) =
    let p = snd (List.nth_exn params i) in
    let ((env',st',s,v), n) = match e with
      | Some expr ->
        (eval_expr ctrl env st SContinue expr, snd p.variable)
      | None ->
        match p.opt_value with
        | Some v -> (eval_expr ctrl env st SContinue v, snd p.variable)
        | None -> (env, st, SContinue, VNull), snd p.variable in
    match (sign,s) with
    | SContinue,SContinue -> ((env',st',s), (n,v))
    | SReject _, _ -> ((env,st,sign),(n,VNull))
    | _, SReject _ -> ((env',st',s),(n,VNull))
    | _ -> failwith "unreachable"

  and insert_arg (e : EvalEnv.t) (p : TypeParameter.t) ((name,v) : string * value) : env =
    let var = Types.BareName (snd p).variable in
    EvalEnv.insert_val var v e

  and copy_arg_out (inc_next : bool) (ctrl : ctrl) (st : state) (fenv : env)
      (e : env) (p : TypeParameter.t) (a : Expression.t option) : env =
    match (snd p).direction with
    | Directionless ->
      begin match (snd p).typ with 
        | Extern _ -> copy_arg_out_h inc_next ctrl fenv st e p a
        | _ -> e
      end
    | InOut
    | Out -> copy_arg_out_h inc_next ctrl fenv st e p a
    | In -> e

  and copy_arg_out_h (inc_next : bool) (ctrl : ctrl) (fenv : env) (st : state)
      (e : env) (p : TypeParameter.t) (a : Expression.t option) : env =
    let v = EvalEnv.find_val (BareName (snd p).variable) fenv in
    match a with
    | None -> e
    | Some expr -> 
      let (_, _, _, lv) = lvalue_of_expr ctrl e st SContinue expr in
      (assign_lvalue e (Option.value_exn lv) v inc_next) |> fst
  (*----------------------------------------------------------------------------*)
  (* Built-in Function Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_builtin (ctrl : ctrl) (env : env) (st : state) (name : string) (lv : lvalue)
      (args : Expression.t option list) : env * state * signal * value =
    match name with
    | "isValid"    -> eval_isvalid ctrl env st lv
    | "setValid"   -> eval_setbool ctrl env st lv true
    | "setInvalid" -> eval_setbool ctrl env st lv false
    | "pop_front"  -> eval_popfront ctrl env st lv args
    | "push_front" -> eval_pushfront ctrl env st lv args
    | "apply"      -> 
      let lvname = match lv.lvalue with LName {name} -> name | _ -> failwith "bad apply" in
      let (s,v) = value_of_lvalue env lv in 
      let (env', st', s, v) =
        eval_app ctrl (EvalEnv.set_namespace (name_only lvname) env) st s v args
      in
      EvalEnv.set_namespace (EvalEnv.get_namespace env) env', st', s, v
    | _ -> failwith "builtin unimplemented"

  and eval_isvalid (ctrl : ctrl) (env : env) (st : state) 
      (lv : lvalue) : env * state * signal * value =
    let (s,v) = value_of_lvalue env lv in
    match s, v with
    | (SReturn _ | SExit | SReject _), _ -> (env, st, s, VNull)
    | SContinue, VHeader{is_valid=b;_} ->
       (env, st, s, VBool b)
    | SContinue, VUnion{fields} ->
       let field_valid (_, v) = snd (assert_header v) in
       let valid = List.exists ~f:field_valid fields in
       (env, st, s, VBool valid)
    | SContinue, _ ->
       failwith "isvalid call is not a header"

  and eval_setbool (ctrl : ctrl) (env : env) (st : state) (lv : lvalue)
      (b : bool) : env * state * signal * value =
    let (s,v) = value_of_lvalue env lv in
    match s, v with
    | (SReturn _ | SExit | SReject _), _ -> (env, st, s, VNull)
    | SContinue, VHeader hdr ->
       let env, signal = assign_lvalue env lv (VHeader {hdr with is_valid = b}) false in
       (env, st, signal, VBool b)
    | SContinue, _ ->
       failwith "isvalid call is not a header"

  and eval_popfront (ctrl : ctrl) (env : env) (st : state) (lv : lvalue)
      (args : Expression.t option list) : env * state * signal * value =
    eval_push_pop ctrl env st lv args false

  and eval_pushfront (ctrl : ctrl) (env : env) (st : state) (lv : lvalue)
      (args : Expression.t option list) : env * state * signal * value =
    eval_push_pop ctrl env st lv args true

  and eval_push_pop (ctrl : ctrl) (env : env) (st : state) (lv : lvalue)
      (args : Expression.t option list) (b : bool) : env * state * signal * value =
    let (env', st', s, a) = eval_push_pop_args ctrl env st args in
    let (s',v) = value_of_lvalue env lv in
    let (hdrs, size, next) =
      match v with
      | VStack{headers=hdrs;size;next} -> (hdrs,size,next)
      | _ -> failwith "push call not a header stack" in
    let x = if b then Bigint.(size - a) else a in
    let (hdrs1, hdrs2) = List.split_n hdrs Bigint.(to_int_exn x) in
    let t = typ_of_stack_mem env lv in
    let hdrs0 = List.init (Bigint.to_int_exn a) ~f:(fun x -> init_val_of_typ env' t) in
    let hdrs' = if b then hdrs0 @ hdrs1 else hdrs2 @ hdrs0 in
    let y = if b then Bigint.(next + a) else Bigint.(next-a) in
    let v = VStack{headers=hdrs';size;next=y} in
    match s,s' with
    | SContinue, SContinue -> 
      let (e,_) = assign_lvalue env lv v false in (e,st', s, VNull)
    | SReject _, _ -> (env',st',s,VNull)
    | _, SReject _ -> (env',st',s',VNull)
    | _ -> failwith "unreachble"

  and eval_push_pop_args (ctrl : ctrl) (env : env) (st : state) 
      (args : Expression.t option list) : env * state * signal * Bigint.t =
    match args with
    | [Some value] ->
      let (env', st', s, v) = eval_expr ctrl env st SContinue value in
      begin match s with
        | SContinue -> (env', st', s, bigint_of_val v)
        | SReject _ -> (env', st', s, Bigint.zero)
        | _ -> failwith "unreachable" end
    | _ -> failwith "invalid push or pop args"

  (*----------------------------------------------------------------------------*)
  (* Parser Evaluation *)
  (*----------------------------------------------------------------------------*)

  and eval_parser (ctrl : ctrl) (env : env) (st : state) (params : TypeParameter.t list)
      (args : Expression.t option list) (vs : (string * value) list)
      (locals : Declaration.t list) (states : Parser.state list) : env * state * signal =
    let (penv, st', s) = copyin ctrl env st params args in
    match s with
    | SContinue ->
      let f a (x,y) = EvalEnv.insert_val_bare x y a in
      let penv' = List.fold_left vs ~init:penv ~f:f in
      let (penv'', st'') = List.fold_left locals ~init:(penv',st') ~f:(fun (e,s) -> eval_decl ctrl e s) in
      let states' = List.map states ~f:(fun s -> snd (snd s).name, s) in
      let start = find_exn states' "start" in
      let (penv''', st''', final_state) = eval_state_machine ctrl penv'' st'' states' start in
      (copyout ctrl penv''' st''' params args false, st''', final_state)
    | SReject _ -> (EvalEnv.pop_scope penv, st, s)
    | _ -> failwith "unreachable"

  and eval_state_machine (ctrl : ctrl) (env : env) (st : state)
      (states : (string * Parser.state) list)
      (state : Parser.state) : env * state * signal =
    let (stms, transition) =
      match snd state with
      | {statements=stms; transition=t;_} -> (stms, t) in
    let open Statement in
    let stms' = Info.dummy, {stmt = Statement.BlockStatement
                  {block = (Info.dummy, {annotations = []; statements = stms})};
                typ = Unit} in
    let (env', st', sign) = eval_stmt ctrl env st SContinue stms' in
    match sign with
    | SContinue -> eval_transition ctrl env' st' states transition
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
      (states : (string * Parser.state) list) 
      (next : string) : env * state * signal =
    match next with
    | "accept" -> (env, st, SContinue)
    | "reject" -> (env, st, SReject "NoError")
    | _ -> let state = find_exn states next in
          eval_state_machine ctrl env st states state

  and eval_select (ctrl : ctrl) (env : env) (st : state)
      (states : (string * Parser.state) list) (exprs : Expression.t list)
      (cases : Parser.case list) : env * state * signal =
    let f (env,st,s) e =
      let (a,b,c,d) = eval_expr ctrl env st s e in
      ((a,b,c),d) in
    let ((env', st', s), vs) = List.fold_map exprs ~init:(env,st,SContinue) ~f:f in
    let ws = List.map vs ~f:width_of_val in
    match s with
    | SContinue ->
      let g (e,st,s) set =
        let (w,x,y,z) = set_of_case ctrl e st s set ws in
        ((w,x,y),(z,w,x)) in
      let ((env'',st'', s), ss) = List.fold_map cases ~init:(env', st', SContinue) ~f:g in
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
      let ms = List.map ss' ~f:(fun (x,y,z) -> (values_match_set vs x, y,z)) in
      let ms' = List.zip_exn ms cases
                |> List.map ~f:(fun ((b,env,st),c) -> (b,(env,st,c))) in
      let next = List.Assoc.find ms' true ~equal:Poly.(=) in
      begin match next with
        | None -> (env'', st', SReject "NoMatch")
        | Some (fenv,st,next) ->
          let next' = snd (snd next).next in
          eval_direct ctrl fenv st states next' end
    | SReject _ -> (env',st', s)
    | _ -> failwith "unreachable"

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
          let (env', st', s, v) = eval_expr ctrl env st SContinue expr in
          (env', st', s, assert_set v w) end
    | SReject _ -> (env, st, s, SUniversal)
    | _ -> failwith "unreachable"

  and values_match_set (vs : value list) (s : set) : bool =
    match s with
    | SSingleton{w;v}     -> values_match_singleton vs v
    | SUniversal          -> true
    | SMask{v=v1;mask=v2} -> values_match_mask vs v1 v2
    | SRange{lo=v1;hi=v2} -> values_match_range vs v1 v2
    | SProd l             -> values_match_prod vs l
    | SLpm{w=v1;v=v2;_}   -> values_match_mask vs v1 v2
    | SValueSet {sets=ss;_}   -> values_match_value_set vs ss

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

  and values_match_range (vs : value list) (low_bound : value) (high_bound : value) : bool =
    let v = bigint_of_val (assert_singleton vs) in
    let low_bound = bigint_of_val low_bound in
    let high_bound = bigint_of_val high_bound in
    Bigint.(low_bound <= v && v <= high_bound)

  and values_match_prod (vs : value list) (l : set list) : bool =
    let bs = List.mapi l ~f:(fun i x -> values_match_set [List.nth_exn vs i] x) in
    List.for_all bs ~f:(fun b -> b)

  and values_match_value_set (vs : value list) (l : set list) : bool =
    let bs = List.map l ~f:(values_match_set vs) in
    List.exists bs ~f:(fun b -> b)

  (* -------------------------------------------------------------------------- *)
  (* Control Evaluation *)
  (* -------------------------------------------------------------------------- *)

  and eval_control (ctrl : ctrl) (env : env) (st : state) (params : TypeParameter.t list)
      (args : Expression.t option list) (vs : (string * value) list)
      (locals : Declaration.t list) (apply : Block.t) : env * state * signal =
    let open Statement in
    let (cenv,st',_) = copyin ctrl env st params args in
    let f a (x,y) = EvalEnv.insert_val_bare x y a in
    let cenv' = List.fold_left vs ~init:cenv ~f:f in
    let (cenv'',st'') = List.fold_left locals ~init:(cenv',st') ~f:(fun (e,st) s -> eval_decl ctrl e st s) in
    let block = 
      (Info.dummy,
      {stmt = Statement.BlockStatement {block = apply};
      typ = Unit}) in
    let (cenv''', st''', sign) = eval_stmt ctrl cenv'' st'' SContinue block in
    match sign with
    | SContinue
    | SReject _
    | SReturn VNull
    | SExit     -> (copyout ctrl cenv''' st''' params args false, st''', sign)
    | SReturn _ -> failwith "control should not return"

  (*----------------------------------------------------------------------------*)
  (* Helper functions *)
  (*----------------------------------------------------------------------------*)

  and fourth4 (a,b,c,d : 'a * 'b * 'c * 'd) : 'd = d

  and assert_singleton (vs : value list) : value =
    match vs with
    | [v] -> v
    | _ -> failwith "value list has more than one element"

  and assert_some (x : 'a option) : 'a =
    match x with
    | None -> failwith "is none"
    | Some v -> v

  and assert_typ (typ_or_decl : (Type.t, Declaration.t) Util.alternative) : Type.t =
    match typ_or_decl with
    | Left typ -> typ
    | Right decl -> failwith "not a typ"

  and assert_typ_def (typ : Declaration.t) : (Type.t, Declaration.t) Util.alternative =
    match snd typ with
    | TypeDef {typ_or_decl;_} -> typ_or_decl
    | _ -> failwith "not a typedef"

  and is_extern_object (d : Declaration.t) : bool = 
    match snd d with 
    | ExternObject _ -> true 
    | _ -> false

  and init_binding_of_field (ctrl : ctrl) (env : env) (st : state)
      (f : Declaration.field) : string * value =
    snd (snd f).name, init_val_of_typ env (snd f).typ

  and typ_of_stack_mem (env : env) (lv : lvalue) : Type.t =
    match lv.typ with
    | Array{typ;_} -> typ
    | _ -> failwith "not a header stack"

  and struct_of_list (ctrl : ctrl) (env : env) (st : state) (t : Type.t)
      (l : value list) : value =
    let (fs) = match t with
      | Struct s ->  s.fields
      | _ -> failwith "not a struct" in
    let ns = List.map fs ~f:(fun x -> x.name) in
    let ts = List.map fs ~f:(fun x -> x.typ) in
    let l' = List.mapi l ~f:(fun i v -> implicit_cast_from_rawint env v (List.nth_exn ts i)) in
    let l'' = List.mapi l' ~f:(fun i v -> implicit_cast_from_tuple env v (List.nth_exn ts i)) in
    let l''' = List.mapi l'' ~f:(fun i v -> (List.nth_exn ns i, v)) in
    VStruct{fields=l'''}

  and header_of_list (ctrl : ctrl) (env : env) (st : state) (t : Type.t)
      (l : value list) : value =
    let (fs) = match t with
      | Header h -> h.fields
      | _ -> failwith "not a header" in
    let ns = List.map fs ~f:(fun x -> x.name) in
    let ts = List.map fs ~f:(fun x -> x.typ) in
    let l' = List.mapi l ~f:(fun i v -> implicit_cast_from_rawint env v (List.nth_exn ts i)) in
    let l'' = List.mapi l' ~f:(fun i v -> (List.nth_exn ns i, v)) in
    VHeader{fields=l'';is_valid=true}

  and label_matches_string (s : string) (case : Statement.pre_switch_case) : bool =
    match case with
    | Action{label;_}
    | FallThrough{label} ->
      begin match snd label with
        | Default -> true
        | Name(_,n) -> String.equal s n end

  and eval_statement ctrl env st s = 
    let (a,b,_) = eval_stmt ctrl env st SContinue s in (a,b)

  and eval_expression ctrl env st expr = 
    let (a,b,_,c) = eval_expr ctrl env st SContinue expr in (a,b,c)

  and eval (ctrl : ctrl) (env : env) (st : state) (pkt : pkt)
      (in_port : Bigint.t) : state * env * pkt option =
    let env' = T.initialize_metadata in_port env in 
    T.eval_pipeline ctrl env' st pkt eval_app

  and eval_main (ctrl : ctrl) (env : env) (st : state) (pkt : pkt)
      (in_port : Bigint.t) : state * pkt option * Bigint.t =
    let (st', env', pkt) = eval ctrl env st pkt in_port in
    begin match EvalEnv.find_val (BareName (Info.dummy, "std_meta")) env' with
    | VStruct {fields;_} -> 
      st', pkt, 
      find_exn fields "egress_port"
      |> assert_bit
      |> snd
    | _ -> failwith "TODO" end

  and eval_prog (ctrl : ctrl) (env: env) (state : state) (pkt : buf) 
      (in_port : Bigint.t) (prog : program) : state * (buf * Bigint.t) option =
    let (>>|) = Option.(>>|) in
    match prog with Program l ->
    let (env,st) = 
      List.fold_left l 
        ~init:(env, state)
        ~f:(fun (e,s) -> eval_decl ctrl e s) 
    in
    let pkt = {emitted = Cstruct.empty; main = pkt; in_size = Cstruct.len pkt} in
    let st', pkt', port = eval_main ctrl env st pkt in_port in
    st', pkt' >>| fun pkt' -> (Cstruct.append pkt'.emitted pkt'.main, port)

end

(*----------------------------------------------------------------------------*)
(* Program Evaluation *)
(*----------------------------------------------------------------------------*)

module V1Interpreter = MakeInterpreter(V1model.V1Switch)

(* module EbpfInterpreter = MakeInterpreter(Target.EbpfFilter) *)
