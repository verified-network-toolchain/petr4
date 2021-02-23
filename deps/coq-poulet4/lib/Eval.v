Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Strings.String.

Require Import Equations.Equations.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.
Require Import Monads.Transformers.

Require Petr4.String.
Require Petr4.StringConstants.
Require Import Petr4.Environment.
Require Import Petr4.Syntax.
Require Import Petr4.Typed.
Require Import Petr4.Utils.
Require Import Petr4.Unpack.
Require Import Petr4.Platform.Packet.

Import ListNotations.

Open Scope string_scope.
Open Scope monad.

Section Eval.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).
  Notation env_monad := (env_monad tags_t).
  Notation P4String := (P4String.t tags_t).
  Notation Value := (@Value tags_t).
  Notation KeyValue := (@KeyValue tags_t).
  Notation ValueLvalue := (@ValueLvalue tags_t).
  Notation P4Type := (@P4Type tags_t).
  Notation P4Parameter := (@P4Parameter tags_t).
  Notation Expression := (@Expression tags_t).
  Notation ExpressionPreT := (@ExpressionPreT tags_t).
  Notation Block := (@Block tags_t).
  Notation Statement := (@Statement tags_t).
  Notation StatementPreT := (@StatementPreT tags_t).
  Notation Match := (@Match tags_t).
  Notation ParserCase := (@ParserCase tags_t).
  Notation ParserTransition := (@ParserTransition tags_t).

  Definition default_value (A: P4Type) : Value.
  Admitted.

  Definition eval_lvalue (expr: Expression) : env_monad ValueLvalue :=
    let '(MkExpression _ expr' type _) := expr in
    match expr' with
    | ExpName name => mret (MkValueLvalue (ValLeftName name) type)
    | ExpExpressionMember _ _
    | ExpArrayAccess _ _
    | ExpBitStringAccess _ _ _ =>
      state_fail (SupportError "Unimplemented lvalue expression.")
    | _ => state_fail (TypeError "Cannot evaluate this expression as an lvalue.")
    end.

  Definition bvector_negate {n: nat} (b: Bvector n) : Bvector n.
  Admitted.

  Definition bvector_add {n: nat} (x y: Bvector n) : Bvector n.
  Admitted.

  Definition eq_value (v1 v2: Value) : bool.
  Admitted.

  Definition eval_minus (v: Value) : env_monad Value :=
    match v with
    | ValBase (ValBaseBit width bits) => mret (ValBase (ValBaseBit width (Z.opp bits)))
    | ValBase (ValBaseInt width bits) => mret (ValBase (ValBaseInt width (Z.opp bits)))
    | ValBase (ValBaseInteger n) => mret (ValBase (ValBaseInteger (Z.opp n)))
    | _ => state_fail (TypeError "Cannot compute unary negation of this value.")
    end.

  Definition bvec_of_z (width: nat) (z: Z) : (Bvector width).
  Admitted.

  Definition eval_is_valid (lvalue: ValueLvalue) : env_monad Value :=
    let* (_, valid) := unpack_header _ (env_lookup _ lvalue) in
    mret (ValBase (ValBaseBool valid)).

  Definition eval_set_bool (lvalue: ValueLvalue) (valid: bool) : env_monad unit :=
    let* (fields, _) := unpack_header _ (env_lookup _ lvalue) in
    env_update _ lvalue (ValBase (ValBaseHeader fields valid)).

  Definition eval_pop_front (lvalue: ValueLvalue) (args: list (option Value)) : env_monad unit :=
    match args with
    | Some arg :: nil =>
      let* count := unpack_inf_int _ (mret arg) in
      let* '(elements, size, next_index) := unpack_header_stack _ (env_lookup _ lvalue) in
      let padding := ValBaseHeader [] false in
      let* elements' := lift_opt (AssertError "Cannot rotate left by a negative amount.") (rotate_left_z elements count padding) in
      let next_index' := next_index - (Z.to_nat count) in
      let value' := ValBase (ValBaseStack elements' size next_index') in
      env_update _ lvalue value'
    | _ => state_fail (AssertError "Not enough arguments to pop_front.")
    end.

  Definition eval_push_front (lvalue: ValueLvalue) (args: list (option Value)) : env_monad unit :=
    match args with
    | Some arg :: nil =>
      let* count := unpack_inf_int _ (mret arg) in
      let* '(elements, size, next_index) := unpack_header_stack _ (env_lookup _ lvalue) in
      let padding := ValBaseHeader [] false in
      let* elements' := lift_opt (AssertError "Cannot rotate right by a negative amount.") (rotate_right_z elements count padding) in
      let next_index' := min size (next_index + (Z.to_nat count)) in
      let value' := ValBase (ValBaseStack elements' size next_index') in
      env_update _ lvalue value'
    | _ => state_fail (AssertError "Not enough arguments to push_front.")
    end.

  Definition is_packet_func (str: String.t) : bool :=
    if String.eqb str StringConstants.extract
    then true
    else false.

  Definition eval_packet_func (obj: ValueLvalue) (name: String.t) (type_args: list P4Type) (args: list (option Value)) : env_monad unit :=
    let* bits := unpack_packet _ (env_lookup _ obj) in
    if String.eqb name StringConstants.extract then
      match (args, type_args) with
      | ((Some target_expr) :: _, into :: _) =>
        match eval_packet_extract_fixed tags_t into bits with
        | (inr error, bits') =>
          env_update _ obj (ValObj (ValObjPacket bits')) ;;
          state_fail error
        | (inl value, bits') =>
          env_update _ obj (ValObj (ValObjPacket bits')) ;;
          let* target := unpack_lvalue _ (mret target_expr) in
          env_update _ target (ValBase value)
        end
      | _ => state_fail (AssertError "Not enough arguments to extract.")
      end
    else if String.eqb name StringConstants.lookahead then
      state_fail (SupportError "Packet lookahead is not implemented.")
    else if String.eqb name StringConstants.advance then
      state_fail (SupportError "Packet advance is not implemented.")
    else if String.eqb name StringConstants.length then
      state_fail (SupportError "Packet length is not implemented.")
    else
      state_fail (AssertError "Unknown method called on a packet.")
    .

  Definition eval_builtin_func (name: P4String) (obj: ValueLvalue) (type_args : list P4Type) (args: list (option Value)) : env_monad Value :=
    let name := P4String.str name in
    if String.eqb name StringConstants.isValid then
      eval_is_valid obj
    else if String.eqb name StringConstants.setValid then
      dummy_value _ (eval_set_bool obj true)
    else if String.eqb name StringConstants.setInvalid then
      dummy_value _ (eval_set_bool obj false)
    else if String.eqb name StringConstants.pop_front then
      dummy_value _ (eval_pop_front obj args)
    else if String.eqb name StringConstants.push_front then
      dummy_value _ (eval_push_front obj args)
    else if is_packet_func name then
      dummy_value _ (eval_packet_func obj name type_args args)
    else state_fail (SupportError "Unknown built-in function.")
  .

  Definition eval_extern_func (name: String.t) (obj: ValueLvalue) (type_args: list P4Type) (args: list (option Expression)): env_monad Value.
  Admitted.
  (* TODO fix
  let* Packet bits := unpack_extern_obj (find_lvalue obj) in
  dummy_value (eval_packet_func obj name bits type_args args).
   *)

  Definition extract_value_func (caller: ValueLvalue): Value :=
    let func_name := {|P4String.tags := tags_dummy;
                       P4String.str := StringConstants.extract|} in
    let func_impl := ValFuncImplBuiltin func_name caller in
    let param_name := {|P4String.tags := tags_dummy;
                        P4String.str := "headerLvalue"|} in
    let param := MkParameter false Out TypVoid None param_name in
    ValObj (ValObjFun (param :: nil) func_impl)
  .

  Section eval_arguments.
    Variable (eval_expression: Expression -> env_monad Value).

    Equations eval_arguments
      (params: list P4Parameter)
      (args: list (option Expression))
      : env_monad (list (option Value))
      by struct args
    :=
      eval_arguments nil nil :=
        mret nil;
      eval_arguments (param :: params) (Some arg :: args) :=
        let '(MkParameter _ dir _ _ _) := param in
        let* val := match dir with
        | In => eval_expression arg
        | Out =>
          let* lvalue := eval_lvalue arg
          in mret (ValLvalue lvalue)
        (* TODO: Handle InOut and Directionless *)
        | _ => state_fail (SupportError "Unsupported parameter direction.")
        end in
        let* vals := eval_arguments params args in
        mret (Some val :: vals);
      eval_arguments (param :: params) (None :: args) :=
        let* vals := eval_arguments params args in
        mret (None :: vals);
      eval_arguments _ _ :=
        state_fail (AssertError "Mismatch between argument and parameter count.")
    .
  End eval_arguments.

  Section eval_method_call.
    Variable (eval_expression: Expression -> env_monad Value).

    Definition eval_method_call
      (func: Expression)
      (type_args: list P4Type)
      (args: list (option Expression))
      : env_monad Value
    :=
      let* (params, impl) := unpack_func _ (eval_expression func) in
      (* TODO: Properly implement copy in/copy out semantics. *)
      let* args' := eval_arguments (eval_expression) params args in
      match impl with
      | ValFuncImplBuiltin name obj =>
        eval_builtin_func name obj type_args args'
      (* TODO: other function types *)
      (* | ValFuncImplExtern _ name caller => eval_extern_func name obj type_args args' *)
      | _ => state_fail (SupportError "Unsupported function type.")
      end
    .
  End eval_method_call.

  Equations eval_expression (expr: Expression) : env_monad Value :=
    eval_expression (MkExpression expr _ _) :=
      eval_expression_pre expr
  with eval_expression_pre (expr: ExpressionPreT) : env_monad Value :=
    eval_expression_pre (ExpBool value) :=
      mret (ValBase (ValBaseBool value));
    eval_expression_pre (ExpInt value) :=
      match value.(P4Int.width_signed) with
      | Some (width, true) =>
        mret (ValBase (ValBaseInt width value.(P4Int.value)))
      | Some (width, false) =>
        mret (ValBase (ValBaseBit width value.(P4Int.value)))
      | None =>
        mret (ValBase (ValBaseInteger value.(P4Int.value)))
      end;
    eval_expression_pre (ExpString s) :=
      mret (ValBase (ValBaseString s));
    eval_expression_pre (ExpArrayAccess array index) :=
      let* index' := unpack_inf_int _ (eval_expression index) in
      let* array' := unpack_array _ (eval_expression array) in
      match index_z_error array' index' with
      | Some element' => mret (ValBase element')
      | None => state_fail (AssertError "Out-of-bounds array read.")
      end;
    (* TODO: These cases recursively call eval_expression (either directly or
       indirectly), which produces a Value. The values that these cases are
       meant to produce, however, can only contain instances of ValueBase as a
       result of stratification in the definition of values. To get around
       this, we need to similarly stratify our definition of expressions.  *)
    (* eval_expression_pre (ExpList _ exprs) :=
      lift_monad (ValTuple _) (sequence (List.map eval_expression exprs)) *)
    (* eval_expression_pre (ExpRecord entries) :=
      let actions := List.map eval_kv entries in
      lift_monad (ValRecord) (sequence actions); *)
    eval_expression_pre (ExpUnaryOp op arg) :=
      match op with
      | Not =>
        let* b := unpack_bool _ (eval_expression arg) in
        mret (ValBase (ValBaseBool (negb b)))
      | BitNot =>
        let* (w, bits) := unpack_fixed_bits _ (eval_expression arg )in
        mret (ValBase (ValBaseBit w (BinInt.Z.lnot bits)))
      | UMinus =>
        let* inner := eval_expression arg in
        let* negation := eval_minus inner in
        mret negation
      end;
    eval_expression_pre (ExpExpressionMember inner name) :=
      let* inner_v := eval_expression inner in
      match inner_v with
      | ValObj (ValObjPacket bits) =>
        match inner with
        | MkExpression _ (ExpName inner_name) inner_typ _ =>
          if P4String.eq_const name StringConstants.extract then
            mret (extract_value_func (MkValueLvalue (ValLeftName inner_name) inner_typ))
          else if P4String.eq_const name StringConstants.lookahead then
            state_fail (SupportError "Packet lookahead is not implemented.")
          else if P4String.eq_const name StringConstants.advance then
            state_fail (SupportError "Packet advance is not implemented.")
          else if P4String.eq_const name StringConstants.length then
            state_fail (SupportError "Packet length is not implemented.")
          else state_fail (AssertError "Unknown member of packet extern.")
        | _ => state_fail (SupportError "Can only look up members of names.")
        end
      (* TODO real member lookup *)
      | _ => state_fail (SupportError "Can only look up members of a packet.")
      end;
    eval_expression_pre (ExpFunctionCall func type_args args) :=
      eval_method_call (eval_expression) func type_args args;
    eval_expression_pre (ExpName name) :=
      get_name_loc _ name >>= heap_lookup _;
    eval_expression_pre _ :=
      (* TODO *)
      state_fail (SupportError "Unimplemented expression type")
  (* TODO: see comment above *)
  (* with eval_kv (kv: KeyValue) : env_monad (P4String * Value) :=
    eval_kv (MkKeyValue key expr) :=
      let* value := eval_expression expr in
      mret (key, value) *)
  .

  Equations eval_statement (stmt: Statement) : env_monad unit :=
    eval_statement (MkStatement _ stmt _) :=
      eval_statement_pre stmt
  with eval_statement_pre (stmt: StatementPreT) : env_monad unit :=
    eval_statement_pre (StatMethodCall func type_args args) :=
      @toss_value tags_t (eval_method_call eval_expression func type_args args);
    eval_statement_pre (StatAssignment lhs rhs) :=
      let* lval := eval_lvalue lhs in
      let* val := eval_expression rhs in
      env_update _ lval val;
    eval_statement_pre (StatBlock block) :=
      stack_push _ ;;
      eval_block block ;;
      stack_pop _;
    eval_statement_pre (StatConstant type name init) :=
      env_insert _ name.(P4String.str) (ValBase init);
    eval_statement_pre (StatVariable type name init) :=
      let* value :=
         match init with
         | None => mret (default_value type)
         | Some expr => eval_expression expr
         end
      in
      env_insert _ name.(P4String.str) value;
    eval_statement_pre StatEmpty :=
      mret tt;
    eval_statement_pre _ :=
      state_fail (SupportError "Unimplemented statement type")
  with eval_block (blk: Block) : env_monad unit :=
    eval_block BlockEmpty :=
      mret tt;
    eval_block (BlockCons stmt rest) :=
      eval_statement stmt;;
      eval_block rest
  .

  (* TODO: sophisticated pattern matching for the match expression as needed *)
  Fixpoint eval_match_expression (vals: list Value) (matches: list Match) : env_monad bool :=
    match (vals, matches) with
    | (List.nil, List.nil) => mret true
    | (v :: vals', MkMatch _ m _ :: matches') =>
      match m with
      | MatchDontCare => eval_match_expression vals' matches'
      | MatchExpression e =>
        let* v' := eval_expression e in
        if eq_value v v' then eval_match_expression vals' matches' else mret false
      end
    | _ => mret false
    end.

  Fixpoint eval_cases (vals: list Value) (cases: list ParserCase) : env_monad P4String :=
    match cases with
    | List.nil    => state_fail (AssertError "No cases to evaluate against.")
    | MkParserCase _ matches next :: cases' =>
      let* passes := eval_match_expression vals matches in
      if passes then mret next else eval_cases vals cases'
    end.

  Definition eval_transition (t: ParserTransition) : env_monad P4String :=
    match t with
    | ParserDirect _ next =>
      mret next
    | ParserSelect _ exprs cases =>
      let* vs := sequence (List.map eval_expression exprs) in
      eval_cases vs cases
    end.

End Eval.
