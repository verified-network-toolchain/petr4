Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.

Require Petr4.String.
Require Petr4.StringConstants.
Require Import Petr4.Environment.
Require Import Petr4.Syntax.
Require Import Petr4.Typed.
Require Import Petr4.Utils.
Require Import Petr4.Unpack.
Require Import Petr4.Platform.Packet.

Import ListNotations.
Open Scope monad.

Section Eval.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).
  Notation env_monad := (env_monad tags_t).
  Notation P4String := (P4String.t tags_t).
  Notation Value := (Value tags_t).
  Notation KeyValue := (KeyValue tags_t).
  Notation ValueLvalue := (ValueLvalue tags_t).
  Notation P4Type := (P4Type tags_t).
  Notation Expression := (Expression tags_t).
  Notation Block := (Block tags_t).
  Notation Statement := (Statement tags_t).
  Notation Match := (Match tags_t).
  Notation ParserCase := (ParserCase tags_t).
  Notation ParserTransition := (ParserTransition tags_t).

  Definition default_value (A: P4Type) : Value.
  Admitted.

  Definition eval_lvalue (expr: Expression) : env_monad ValueLvalue.
  Admitted.

  Definition bvector_negate {n: nat} (b: Bvector n) : Bvector n.
  Admitted.

  Definition bvector_add {n: nat} (x y: Bvector n) : Bvector n.
  Admitted.

  Definition eq_value (v1 v2: Value) : bool.
  Admitted.

  Definition eval_minus (v: Value) : option Value := 
    match v with
    | ValBase _ (ValBaseBit _ width bits) => Some (ValBase _ (ValBaseBit _ width (Z.opp bits)))
    | ValBase _ (ValBaseInt _ width bits) => Some (ValBase _ (ValBaseInt _ width (Z.opp bits)))
    | ValBase _ (ValBaseInteger _ n) => Some (ValBase _ (ValBaseInteger _ (Z.opp n)))
    | _ => None
    end.

  Definition bvec_of_z (width: nat) (z: Z) : (Bvector width).
  Admitted.

  Definition extract_value_func (caller: ValueLvalue): Value :=
    let name := {|P4String.tags := tags_dummy;
                  P4String.str := StringConstants.extract|} in
    ValObj _ (ValObjBuiltinFun _ name caller).

  Fixpoint eval_expression (expr: Expression) : env_monad Value :=
    let '(MkExpression _ tags_dummy expr _ _) := expr in
    match expr with
    | ExpBool _ value => mret (ValBase _ (ValBaseBool _ value))
    | ExpInt _ value =>
      match value.(P4Int.width_signed) with
      | Some (width, true) =>
        mret (ValBase _ (ValBaseInt _ width value.(P4Int.value)))
      | Some (width, false) =>
        mret (ValBase _ (ValBaseBit _ width value.(P4Int.value)))
      | None =>
        mret (ValBase _ (ValBaseInteger _ value.(P4Int.value)))
      end
    | ExpString _ s =>
      mret (ValBase _ (ValBaseString _ s))
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
        | ValBase _ (ValBaseBit _ w bits) => mret (ValBase _ (ValBaseBit _ w (BinInt.Z.lnot bits)))
        | _ => state_fail Internal
        end
      | UMinus =>
        let* inner := eval_expression arg in
        lift_option _ (eval_minus inner)
      end
    | ExpExpressionMember _ inner name =>
      let* inner_v := eval_expression inner in
      match inner_v with
      | ValObj _ (ValObjPacket _ bits) => 
        match inner with 
        | MkExpression _ _ (ExpName _ inner_name) inner_typ _ => 
          if P4String.eq_const name StringConstants.extract 
          then mret (extract_value_func
                       (MkValueLvalue _ (ValLeftName _ inner_name) inner_typ))
          else state_fail Internal
        | _ => state_fail Internal
        end
      (* TODO real member lookup *)
      | _ => state_fail Internal
      end
    | _ => mret (ValBase _ (ValBaseBool _ false)) (* TODO *)
    end.

  Definition eval_kv (kv: KeyValue) : env_monad (String.t * Value) :=
    let '(MkKeyValue _ _ key expr) := kv in
    let* value := eval_expression expr in
    mret (key.(P4String.str), value).

  Definition eval_is_valid (lvalue: ValueLvalue) : env_monad Value :=
    let* (_, valid) := unpack_header _ (env_lookup _ tags_dummy lvalue) in
    mret (ValBase _ (ValBaseBool _ valid)).

  Definition eval_set_bool (lvalue: ValueLvalue) (valid: bool) : env_monad unit :=
    let* (fields, _) := unpack_header _ (env_lookup _ tags_dummy lvalue) in
    env_update _ tags_dummy lvalue (ValBase _ (ValBaseHeader _ fields valid)).

  Definition eval_pop_front (lvalue: ValueLvalue) (args: list (option Value)) : env_monad unit :=
    match args with
    | Some (ValBase _ (ValBaseInteger _ count)) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack _ (env_lookup _ tags_dummy lvalue) in
      let padding := ValBaseHeader _ [] false in
      let* elements' := lift_option _ (rotate_left_z elements count padding) in
      let next_index' := next_index - (Z.to_nat count) in
      let value' := ValBase _ (ValBaseStack _ elements' size next_index') in
      env_update _ tags_dummy lvalue value'
    | _ => state_fail Internal
    end.

  Definition eval_push_front (lvalue: ValueLvalue) (args: list (option Value)) : env_monad unit :=
    match args with
    | Some (ValBase _ (ValBaseInteger _ count)) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack _ (env_lookup _ tags_dummy lvalue) in
      let padding := ValBaseHeader _ [] false in
      let* elements' := lift_option _ (rotate_right_z elements count padding) in
      let next_index' := min size (next_index + (Z.to_nat count)) in
      let value' := ValBase _ (ValBaseStack _ elements' size next_index') in
      env_update _ tags_dummy lvalue value'
    | _ => state_fail Internal
    end.

  Fixpoint eval_arguments (args: list (option Expression)) : env_monad (list (option Value)) :=
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

  Definition is_packet_func (str: String.t) : bool := 
    if String.eqb str StringConstants.extract
    then true
    else false.

  Definition eval_packet_func (obj: ValueLvalue) (name: String.t) (type_args: list P4Type) (args: list (option Expression)) : env_monad unit.
  Admitted.

  Definition eval_builtin_func (name: String.t) (obj: ValueLvalue) (type_args : list P4Type) (args: list (option Expression)) : env_monad Value :=
    let* args' := eval_arguments args in
    if String.eqb name StringConstants.isValid
    then eval_is_valid obj
    else if String.eqb name StringConstants.setValid
    then dummy_value _ (eval_set_bool obj true)
    else if String.eqb name StringConstants.setInvalid
    then dummy_value _ (eval_set_bool obj false)
    else if String.eqb name StringConstants.pop_front
    then dummy_value _ (eval_pop_front obj args')
    else if String.eqb name StringConstants.push_front
    then dummy_value _ (eval_push_front obj args')
    else state_fail Internal.

  Definition eval_extern_func (name: String.t) (obj: ValueLvalue) (type_args: list P4Type) (args: list (option Expression)): env_monad Value.
  Admitted.

  Fixpoint eval_block (blk: Block) : env_monad unit :=
    match blk with
    | BlockEmpty _ _ =>
      mret tt
    | BlockCons _ stmt rest =>
      eval_statement stmt;;
      eval_block rest
    end
  with eval_statement (stmt: Statement) : env_monad unit :=
         let 'MkStatement _ _ stmt _ := stmt in
         match stmt with
         | StatMethodCall _ func type_args args =>
           state_fail Internal
         | StatAssignment _ lhs rhs =>
           let* lval := eval_lvalue lhs in
           let* val := eval_expression rhs in
           env_update _ tags_dummy lval val
         | StatBlock _ block =>
           stack_push _ ;;
           eval_block block ;;
           stack_pop _
         | StatConstant _ type name init =>
           env_insert _ name.(P4String.str) (ValBase _ init)
         | StatVariable _ type name init =>
           let* value :=
              match init with
              | None => mret (default_value type)
              | Some expr => eval_expression expr
              end in
           env_insert _ name.(P4String.str) value
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
  Fixpoint eval_match_expression (vals: list Value) (matches: list Match) : env_monad bool :=
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

  Fixpoint eval_cases (vals: list Value) (cases: list ParserCase) : env_monad P4String := 
    match cases with
    | List.nil    => state_fail Internal
    | MkParserCase _ _ matches next :: cases' => 
      let* passes := eval_match_expression vals matches in
      if passes then mret next else eval_cases vals cases'
    end.

  Definition eval_transition (t: ParserTransition) : env_monad P4String := 
    match t with
    | ParserDirect _ _ next =>
      mret next
    | ParserSelect _ _ exprs cases =>
      let* vs := sequence (List.map eval_expression exprs) in 
      eval_cases vs cases
    end.

End Eval.
