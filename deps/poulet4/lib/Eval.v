Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.

Require Import CamlString.
Require Import Environment.
Require Import Syntax.
Require Import Typed.
Require Import Utils.
Require Import Unpack.

Require Import Platform.Packet.
Require Import Strings.String.


Open Scope monad.

Section Eval.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  Definition default_value (A: P4Type) : Value tags_t.
  Admitted.

  Definition eval_lvalue (expr: Expression tags_t) : env_monad tags_t ValueLvalue.
  Admitted.

  Definition bvector_negate {n: nat} (b: Bvector n) : Bvector n.
  Admitted.

  Definition bvector_add {n: nat} (x y: Bvector n) : Bvector n.
  Admitted.

  Definition eq_value (v1 v2: Value tags_t) : bool.
  Admitted.

  Definition eval_minus (v: Value tags_t) : option (Value tags_t) := 
    match v with
    | ValBase _ (ValBaseBit _ width bits) => Some (ValBase _ (ValBaseBit _ width (bvector_negate bits)))
    | ValBase _ (ValBaseInt _ width bits) => Some (ValBase _ (ValBaseInt _ width (bvector_negate bits)))
    | ValBase _ (ValBaseInteger _ n) => Some (ValBase _ (ValBaseInteger _ (Z.opp n)))
    | _ => None
    end.

  Definition bvec_of_z (width: nat) (z: Z) : (Bvector width).
  Admitted.

  Definition extract_value_func (caller: ValueLvalue): Value tags_t := ValObj _ (ValObjBuiltinFun _ StrConstants.extract caller).
  

  Fixpoint eval_expression (expr: Expression tags_t) : env_monad tags_t (Value tags_t) :=
    let '(MkExpression _ tags_dummy expr _ _) := expr in
    match expr with
    | ExpBool _ value => mret (ValBase _ (ValBaseBool _ value))
    | ExpInt _ value =>
      match value with
      | MkP4Int _ _ value (Some (width, true)) =>
        mret (ValBase _ (ValBaseInt _ width (bvec_of_z width value)))
      | MkP4Int _ _ value (Some (width, false)) =>
        mret (ValBase _ (ValBaseBit _ width (bvec_of_z width value)))
      | MkP4Int _ _ value None =>
        mret (ValBase _ (ValBaseInteger _ value))
      end
    | ExpString _ (MkP4String _ _ str) => mret (ValBase _ (ValBaseString _ str))
    | ExpName _ name => find_environment _ (str_of_name_warning_not_safe name)
    | ExpArrayAccess _ array index =>
      let* index' := unpack_inf_int _ (eval_expression index) in
      let* array' := unpack_array _ (eval_expression array) in
      let element := 
        match index_z_error array' index' with
        | Some element' => Some (ValBase _ element')
        | None => None
        end in
      lift_option _ element
    | ExpBitStringAccess _ array hi lo =>
      state_fail Internal
(*     | ExpList _ exprs =>
      lift_monad (ValTuple _) (sequence (List.map eval_expression exprs))
    | ExpRecord _ entries => 
      let actions := List.map eval_kv entries in
      lift_monad (ValRecord _) (sequence actions) *)
    | ExpUnaryOp _ op arg => 
      match op with
      | Not => 
        let* b := unpack_bool _ (eval_expression arg) in
        mret (ValBase _ (ValBaseBool _ (negb b)))
      | BitNot => 
        let* inner := eval_expression arg in
        match inner with
        | ValBase _ (ValBaseBit _ w bits) => mret (ValBase _ (ValBaseBit _ w (Bneg w bits)))
        | ValBase _ (ValBaseVarbit _ m w bits) => mret (ValBase _ (ValBaseVarbit _ m w (Bneg w bits)))
        | _ => state_fail Internal
        end
      | UMinus =>
        let* inner := eval_expression arg in
        lift_option _ (eval_minus inner)
      end
    | ExpExpressionMember _ inner (MkP4String _ _ name) =>
      let* inner_v := eval_expression inner in
      match inner_v with
      | ValObj _ (ValObjPacket _ bits) => 
        match inner with 
        | MkExpression _ _ (ExpName _ inner_name) inner_typ _ => 
          if CamlStringOT.eq_dec name StrConstants.extract 
          then mret (extract_value_func (MkValueLvalue (ValLeftName inner_name) inner_typ))
          else state_fail Internal
        | _ => state_fail Internal
        end
      (* TODO real member lookup *)
      | _ => state_fail Internal
      end
    | _ => mret (ValBase _ (ValBaseBool _ false)) (* TODO *)
    end.

  Definition eval_kv (kv: KeyValue tags_t) : env_monad tags_t (caml_string * (Value tags_t)) :=
    let '(MkKeyValue _ _ (MkP4String _ _ key) expr) := kv in
    let* value := eval_expression expr in
    mret (key, value).

  Definition eval_is_valid (obj: ValueLvalue) : env_monad tags_t (Value tags_t) :=
    let* (_, valid) := unpack_header _ (find_lvalue _ obj) in
    mret (ValBase _ (ValBaseBool _ valid)).

  Definition eval_set_bool (obj: ValueLvalue) (valid: bool) : env_monad tags_t unit :=
    let* (fields, _) := unpack_header _ (find_lvalue _ obj) in
    update_lvalue _ tags_dummy obj (ValBase _ (ValBaseHeader _ fields valid)).

  Definition eval_pop_front (obj: ValueLvalue) (args: list (option (Value tags_t))) : env_monad tags_t unit :=
    match args with
    | Some (ValBase _ (ValBaseInteger _ count)) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack _ (find_lvalue _ obj) in
      let padding := ValBaseHeader _ (MStr.Raw.empty _) false in
      let* elements' := lift_option _ (rotate_left_z elements count padding) in
      let next_index' := next_index - (Z.to_nat count) in
      let value' := ValBase _ (ValBaseStack _ elements' size next_index') in
      update_lvalue _ tags_dummy obj value'
    | _ => state_fail Internal
    end.

  Definition eval_push_front (obj: ValueLvalue) (args: list (option (Value tags_t))) : env_monad tags_t unit :=
    match args with
    | Some (ValBase _ (ValBaseInteger _ count)) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack _ (find_lvalue _ obj) in
      let padding := ValBaseHeader _ (MStr.Raw.empty _) false in
      let* elements' := lift_option _ (rotate_right_z elements count padding) in
      let next_index' := min size (next_index + (Z.to_nat count)) in
      let value' := ValBase _ (ValBaseStack _ elements' size next_index') in
      update_lvalue _ tags_dummy obj value'
    | _ => state_fail Internal
    end.

  Fixpoint eval_arguments (args: list (option (Expression tags_t))) : env_monad tags_t (list (option (Value tags_t))) :=
    match args with
    | nil => mret nil
    | Some arg :: args' =>
      let* val := eval_expression arg in
      let* vals := eval_arguments args' in
      mret (Some val :: vals)
    | None :: args' =>
      let* vals := eval_arguments args' in
      mret (None :: vals)
    end.

  Definition is_packet_func (str: caml_string) : bool := 
    if CamlStringOT.eq_dec str StrConstants.extract
    then true
    else false.

  Definition eval_packet_func (obj: ValueLvalue) (name: caml_string) (type_args: list P4Type) (args: list (option (Expression tags_t))) : env_monad tags_t unit :=
    obj' <- find_lvalue _ obj ;;
    match obj' with
      | ValObj _ (ValObjPacket _ bits) => if CamlStringOT.eq_dec name StrConstants.extract then 
          match (args, type_args) with
          | ((Some target_expr) :: nil, into :: nil) =>
            match eval_packet_extract_fixed tags_t into bits with 
            | (inr error, bits') =>
              update_lvalue _ tags_dummy obj (ValObj _ (ValObjPacket _ bits')) ;;
              state_fail error 
            | (inl value, bits') =>
              update_lvalue _ tags_dummy obj (ValObj _ (ValObjPacket _ bits')) ;;
              let* target := eval_lvalue target_expr in
              update_lvalue _ tags_dummy target (ValBase _ value) ;;
              mret tt
            end
        
          | _ => state_fail Internal
          end

        else state_fail Internal
      | _ => state_fail Internal
    end.

  Definition eval_builtin_func (name: caml_string) (obj: ValueLvalue) (args: list (option (Expression tags_t))) : env_monad tags_t (Value tags_t) :=
    let* args' := eval_arguments args in
    if CamlStringOT.eq_dec name StrConstants.isValid
    then eval_is_valid obj
    else if CamlStringOT.eq_dec name StrConstants.setValid
    then dummy_value _ (eval_set_bool obj true)
    else if CamlStringOT.eq_dec name StrConstants.setInvalid
    then dummy_value _ (eval_set_bool obj false)
    else if CamlStringOT.eq_dec name StrConstants.pop_front
    then dummy_value _ (eval_pop_front obj args')
    else if CamlStringOT.eq_dec name StrConstants.push_front
    then dummy_value _ (eval_push_front obj args')
    else if is_packet_func name 
    then dummy_value _ (eval_packet_func obj name nil args)
    else state_fail Internal.


  
  

  Definition eval_extern_func (name: caml_string) (obj: ValueLvalue) (type_args: list P4Type) (args: list (option (Expression tags_t))): env_monad tags_t (Value tags_t).
  Admitted.
  (* TODO fix
  let* Packet bits := unpack_extern_obj (find_lvalue obj) in
  dummy_value (eval_packet_func obj name bits type_args args).
   *)

  Definition eval_method_call (func: Expression tags_t) (type_args: list P4Type) (args: list (option (Expression tags_t))) : env_monad tags_t (Value tags_t) :=
    let* func' := eval_expression func in
    match func' with
    | ValObj _ (ValObjBuiltinFun _ name obj) => eval_builtin_func name obj args
    (* | ValExternFun name caller params => eval_extern_func name obj type_args args *)
    | _ => state_fail Internal (* TODO: other function types *)
    end.

  Fixpoint eval_block (blk: Block tags_t) : env_monad tags_t unit :=
    match blk with
    | BlockEmpty _ _ =>
      mret tt
    | BlockCons _ stmt rest =>
      eval_statement stmt;;
      eval_block rest
    end
  with eval_statement (stmt: Statement tags_t) : env_monad tags_t unit :=
         let 'MkStatement _ _ stmt _ := stmt in
         match stmt with
         | StatMethodCall _ func type_args args =>
           toss_value _ (eval_method_call func type_args args)
         | StatAssignment _ lhs rhs =>
           let* lval := eval_lvalue lhs in
           let* val := eval_expression rhs in
           update_lvalue _ tags_dummy lval val
         | StatBlock _ block =>
           map_env _ (push_scope _);;
           eval_block block;;
           lift_env_fn _ (pop_scope _)
         | StatConstant _ type (MkP4String _ _ name) init =>
           insert_environment _ name (ValBase _ init)
         | StatVariable _ type (MkP4String _ _ name) init =>
           let* value :=
              match init with
              | None => mret (default_value type)
              | Some expr => eval_expression expr
              end
           in
           insert_environment _ name value
         | StatInstantiation _ _ _ _ _
         | StatDirectApplication _ _ _
         | StatConditional _ _ _ _
         | StatExit _
         | StatEmpty _
         | StatReturn _ _
         | StatSwitch _ _ _ =>
           state_fail Internal
         end.

  (* TODO: sophisticated pattern matching for the match expression as needed *)
  Fixpoint eval_match_expression (vals: list (Value tags_t)) (matches: list (Match tags_t)) : env_monad tags_t bool :=
    match (vals, matches) with
    | (List.nil, List.nil) => mret true
    | (v :: vals', MkMatch _ _ m _ :: matches') => 
      match m with
      | MatchDontCare _ => eval_match_expression vals' matches'
      | MatchExpression _ e => 
        let* v' := eval_expression e in 
        if eq_value v v' then eval_match_expression vals' matches' else mret false
      end
    | _ => mret false
    end.

  Fixpoint eval_cases (vals: list (Value tags_t)) (cases: list (ParserCase tags_t)) : env_monad tags_t caml_string := 
    match cases with
    | List.nil    => state_fail Internal
    | MkParserCase _ _ matches (MkP4String _ _ next) :: cases' => 
      let* passes := eval_match_expression vals matches in
      if passes then mret next else eval_cases vals cases'
    end.

  Definition eval_transition (t: ParserTransition tags_t) : env_monad tags_t caml_string := 
    match t with
    | ParserDirect _ _ (MkP4String _ _ next) =>
      mret next
    | ParserSelect _ _ exprs cases =>
      let* vs := sequence (List.map eval_expression exprs) in 
      eval_cases vs cases
    end.

End Eval.
