Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Strings.String.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.

Require Import Environment.
Require Import Syntax.
Require Import Typed.
Require Import Utils.
Require Import Unpack.

Require Import Platform.Packet.


Open Scope monad.

Section Eval.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  Definition default_value (A: P4Type) : Value tags_t.
  Admitted.

  Definition eval_lvalue (expr: Expression tags_t) : env_monad tags_t (ValueLvalue tags_t).
  Admitted.

  Definition bvector_negate {n: nat} (b: Bvector n) : Bvector n.
  Admitted.

  Definition bvector_add {n: nat} (x y: Bvector n) : Bvector n.
  Admitted.

  Definition eq_value (v1 v2: Value tags_t) : bool.
  Admitted.

  Definition eval_minus (v: Value tags_t) : option (Value tags_t) := 
    match v with
    | ValBit _ width bits => Some (ValBit _ width (bvector_negate bits))
    | ValInt _ width bits => Some (ValInt _ width (bvector_negate bits))
    | ValInteger _ n => Some (ValInteger _ (Z.opp n))
    | _ => None
    end.

  Definition bvec_of_z (width: nat) (z: Z) : (Bvector width).
  Admitted.

  Fixpoint eval_expression (expr: Expression tags_t) : env_monad tags_t (Value tags_t) :=
    let '(MkExpression _ tags_dummy expr _ _) := expr in
    match expr with
    | ExpBool _ value => mret (ValBool _ value)
    | ExpInt _ value =>
      match value with
      | MkP4Int _ _ value (Some (width, true)) =>
        mret (ValInt _ width (bvec_of_z width value))
      | MkP4Int _ _ value (Some (width, false)) =>
        mret (ValBit _ width (bvec_of_z width value))
      | MkP4Int _ _ value None =>
        mret (ValInteger _ value)
      end
    | ExpString _ (MkP4String _ _ str) => mret (ValString _ str)
    | ExpArrayAccess _ array index =>
      let* index' := unpack_inf_int _ (eval_expression index) in
      let* array' := unpack_array _ (eval_expression array) in
      lift_option _ (index_z_error array' index')
    | ExpBitStringAccess _ array hi lo =>
      state_fail Internal
    | ExpList _ exprs =>
      lift_monad (ValTuple _) (sequence (List.map eval_expression exprs))
    | ExpRecord _ entries => 
      let actions := List.map eval_kv entries in
      lift_monad (ValRecord _) (sequence actions)
    | ExpUnaryOp _ op arg => 
      match op with
      | Not => 
        let* b := unpack_bool _ (eval_expression arg) in
        mret (ValBool _ (negb b))
      | BitNot => 
        let* inner := eval_expression arg in
        match inner with
        | ValBit _ w bits => mret (ValBit _ w (Bneg w bits))
        | ValVarbit _ m w bits => mret (ValVarbit _ m w (Bneg w bits))
        | _ => state_fail Internal
        end
      | UMinus =>
        let* inner := eval_expression arg in
        lift_option _ (eval_minus inner)
      end
    | _ => mret (ValBool _ false) (* TODO *)
    end

  with eval_kv (kv: KeyValue tags_t) : env_monad tags_t (string * (Value tags_t)) :=
         let '(MkKeyValue _ _ (MkP4String _ _ key) expr) := kv in
         let* value := eval_expression expr in
         mret (key, value).

  Definition eval_is_valid (obj: (ValueLvalue tags_t)) : env_monad tags_t (Value tags_t) :=
    let* (_, valid) := unpack_header _ (find_lvalue _ obj) in
    mret (ValBool _ valid).

  Definition eval_set_bool (obj: ValueLvalue tags_t) (valid: bool) : env_monad tags_t unit :=
    let* (fields, _) := unpack_header _ (find_lvalue _ obj) in
    update_lvalue _ tags_dummy obj (ValHeader _ fields valid).

  Definition eval_pop_front (obj: ValueLvalue _) (args: list (option (Value tags_t))) : env_monad tags_t unit :=
    match args with
    | Some (ValInteger _ count) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack _ (find_lvalue _ obj) in
      let padding := ValHeader _ (MStr.Raw.empty _) false in
      let* elements' := lift_option _ (rotate_left_z elements count padding) in
      let next_index' := next_index - (Z.to_nat count) in
      let value' := ValStack _ elements' size next_index' in
      update_lvalue _ tags_dummy obj value'
    | _ => state_fail Internal
    end.

  Definition eval_push_front (obj: (ValueLvalue tags_t)) (args: list (option (Value tags_t))) : env_monad tags_t unit :=
    match args with
    | Some (ValInteger _ count) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack _ (find_lvalue _ obj) in
      let padding := ValHeader _ (MStr.Raw.empty _) false in
      let* elements' := lift_option _ (rotate_right_z elements count padding) in
      let next_index' := min size (next_index + (Z.to_nat count)) in
      let value' := ValStack _ elements' size next_index' in
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

  Definition eval_builtin_func (name: string) (obj: (ValueLvalue tags_t)) (args: list (option (Expression tags_t))) : env_monad tags_t (Value tags_t) :=
    let* args' := eval_arguments args in
    match name with
    | "isValid" => eval_is_valid obj
    | "setValid" => dummy_value _ (eval_set_bool obj true)
    | "setInvalid" => dummy_value _ (eval_set_bool obj false)
    | "pop_front" => dummy_value _ (eval_pop_front obj args')
    | "push_front" => dummy_value _ (eval_push_front obj args')
    | _ => state_fail Internal
    end.

  Definition eval_packet_func (obj: (ValueLvalue tags_t)) (name: string) (bits: list bool) (type_args: list P4Type) (args: list (option (Expression tags_t))) : env_monad tags_t unit.
  Admitted.
  (* TODO: Fix the following code to handle the "real" representation of packets. *)
  (*
  match name with
  | "extract" =>
    match (args, type_args) with
    | ((Some target_expr) :: nil, into :: nil) =>
      let* target := eval_lvalue target_expr in
      match eval_packet_extract_fixed into bits with
      | (inr error, bits') =>
        update_lvalue obj (ValExternObj (Packet bits')) ;;
        state_fail error
      | (inl value, bits') =>
        update_lvalue obj (ValExternObj (Packet bits')) ;;
        update_lvalue target value ;;
        mret tt
      end
    | _ => state_fail Internal
    end
  | _ => state_fail Internal
  end.
   *)

  Definition eval_extern_func (name: string) (obj: (ValueLvalue tags_t)) (type_args: list P4Type) (args: list (option (Expression tags_t))): env_monad tags_t (Value tags_t).
  Admitted.
  (* TODO fix
  let* Packet bits := unpack_extern_obj (find_lvalue obj) in
  dummy_value (eval_packet_func obj name bits type_args args).
   *)

  Definition eval_method_call (func: Expression tags_t) (type_args: list P4Type) (args: list (option (Expression tags_t))) : env_monad tags_t (Value tags_t) :=
    let* func' := eval_expression func in
    match func' with
    | ValBuiltinFun _ name obj => eval_builtin_func name obj args
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
           insert_environment _ name init
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

  Fixpoint eval_cases (vals: list (Value tags_t)) (cases: list (ParserCase tags_t)) : env_monad tags_t string := 
    match cases with
    | List.nil    => state_fail Internal
    | MkParserCase _ _ matches (MkP4String _ _ next) :: cases' => 
      let* passes := eval_match_expression vals matches in
      if passes then mret next else eval_cases vals cases'
    end.

  Definition eval_transition (t: ParserTransition tags_t) : env_monad tags_t string := 
    match t with
    | ParserDirect _ _ (MkP4String _ _ next) =>
      mret next
    | ParserSelect _ _ exprs cases =>
      let* vs := sequence (List.map eval_expression exprs) in 
      eval_cases vs cases
    end.

End Eval.
