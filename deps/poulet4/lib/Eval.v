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
  Notation Value := (@Value tags_t).
  Notation KeyValue := (@KeyValue tags_t).
  Notation ValueLvalue := (@ValueLvalue tags_t).
  Notation P4Type := (@P4Type tags_t).
  Notation Expression := (@Expression tags_t).
  Notation Block := (@Block tags_t).
  Notation Statement := (@Statement tags_t).
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
    | ExpBitStringAccess _ _ _ 
    | _ => state_fail Internal
    end.

  Definition bvector_negate {n: nat} (b: Bvector n) : Bvector n.
  Admitted.

  Definition bvector_add {n: nat} (x y: Bvector n) : Bvector n.
  Admitted.

  Definition eq_value (v1 v2: Value) : bool.
  Admitted.

  Definition eval_minus (v: Value) : option Value := 
    match v with
    | ValBase (ValBaseBit width bits) => Some (ValBase (ValBaseBit width (Z.opp bits)))
    | ValBase (ValBaseInt width bits) => Some (ValBase (ValBaseInt width (Z.opp bits)))
    | ValBase (ValBaseInteger n) => Some (ValBase (ValBaseInteger (Z.opp n)))
    | _ => None
    end.

  Definition bvec_of_z (width: nat) (z: Z) : (Bvector width).
  Admitted.

  Definition extract_value_func (caller: ValueLvalue): Value :=
    let name := {|P4String.tags := tags_dummy;
                  P4String.str := StringConstants.extract|} in
    ValObj (ValObjBuiltinFun name caller).

  Fixpoint eval_expression (expr: Expression) : env_monad Value :=
    let '(MkExpression tags_dummy expr _ _) := expr in
    match expr with
    | ExpBool value => mret (ValBase (ValBaseBool value))
    | ExpInt value =>
      match value.(P4Int.width_signed) with
      | Some (width, true) =>
        mret (ValBase (ValBaseInt width value.(P4Int.value)))
      | Some (width, false) =>
        mret (ValBase (ValBaseBit width value.(P4Int.value)))
      | None =>
        mret (ValBase (ValBaseInteger value.(P4Int.value)))
      end
    | ExpString s =>
      mret (ValBase (ValBaseString s))
    | ExpArrayAccess array index =>
      let* index' := unpack_inf_int _ (eval_expression index) in
      let* array' := unpack_array _ (eval_expression array) in
      let element := 
        match index_z_error array' index' with
        | Some element' => Some (ValBase element')
        | None => None
        end in
      lift_option _ element
    | ExpBitStringAccess array hi lo =>
      state_fail Internal
(*     | ExpList _ exprs =>
      lift_monad (ValTuple _) (sequence (List.map eval_expression exprs))
    | ExpRecord _ entries => 
      let actions := List.map eval_kv entries in
      lift_monad (ValRecord _) (sequence actions) *)
    | ExpUnaryOp op arg => 
      match op with
      | Not => 
        let* b := unpack_bool _ (eval_expression arg) in
        mret (ValBase (ValBaseBool (negb b)))
      | BitNot => 
        let* inner := eval_expression arg in
        match inner with
        | ValBase (ValBaseBit w bits) => mret (ValBase (ValBaseBit w (BinInt.Z.lnot bits)))
        | _ => state_fail Internal
        end
      | UMinus =>
        let* inner := eval_expression arg in
        lift_option _ (eval_minus inner)
      end
    | ExpExpressionMember inner name =>
      let* inner_v := eval_expression inner in
      match inner_v with
      | ValObj (ValObjPacket bits) => 
        match inner with 
        | MkExpression _ (ExpName inner_name) inner_typ _ => 
          if P4String.eq_const name StringConstants.extract 
          then mret (extract_value_func
                       (MkValueLvalue (ValLeftName inner_name) inner_typ))
          else state_fail Internal
        | _ => state_fail Internal
        end
      (* TODO real member lookup *)
      | _ => state_fail Internal
      end
    | _ => mret (ValBase (ValBaseBool false)) (* TODO *)
    end.

  Set Printing Implicit.

  Definition eval_kv (kv: KeyValue) : env_monad (String.t * Value) :=
    let '(MkKeyValue _ key expr) := kv in
    let* value := eval_expression expr in
    mret (key.(P4String.str), value).

  Definition eval_is_valid (lvalue: ValueLvalue) : env_monad Value :=
    let* (_, valid) := unpack_header _ (env_lookup _ tags_dummy lvalue) in
    mret (ValBase (ValBaseBool valid)).

  Definition eval_set_bool (lvalue: ValueLvalue) (valid: bool) : env_monad unit :=
    let* (fields, _) := unpack_header _ (env_lookup _ tags_dummy lvalue) in
    env_update _ tags_dummy lvalue (ValBase (ValBaseHeader fields valid)).

  Definition eval_pop_front (lvalue: ValueLvalue) (args: list (option Value)) : env_monad unit :=
    match args with
    | Some (ValBase (ValBaseInteger count)) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack _ (env_lookup _ tags_dummy lvalue) in
      let padding := ValBaseHeader [] false in
      let* elements' := lift_option _ (rotate_left_z elements count padding) in
      let next_index' := next_index - (Z.to_nat count) in
      let value' := ValBase (ValBaseStack elements' size next_index') in
      env_update _ tags_dummy lvalue value'
    | _ => state_fail Internal
    end.

  Definition eval_push_front (lvalue: ValueLvalue) (args: list (option Value)) : env_monad unit :=
    match args with
    | Some (ValBase (ValBaseInteger count)) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack _ (env_lookup _ tags_dummy lvalue) in
      let padding := ValBaseHeader [] false in
      let* elements' := lift_option _ (rotate_right_z elements count padding) in
      let next_index' := min size (next_index + (Z.to_nat count)) in
      let value' := ValBase (ValBaseStack elements' size next_index') in
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

  Definition eval_packet_func (obj: ValueLvalue) (name: String.t) (type_args: list P4Type) (args: list (option Expression)) : env_monad unit :=
    obj' <- env_lookup _ tags_dummy obj ;;
    match obj' with
    | ValObj (ValObjPacket bits) => 
      if String.eqb name String.extract 
      then 
        match (args, type_args) with
        | ((Some target_expr) :: _, into :: _) =>
          match eval_packet_extract_fixed tags_t into bits with 
          | (inr error, bits') =>
            env_update _ tags_dummy obj (ValObj (ValObjPacket bits')) ;;
            state_fail error 
          | (inl value, bits') =>
            env_update _ tags_dummy obj (ValObj (ValObjPacket bits')) ;;
            let* target := eval_lvalue target_expr in
            env_update _ tags_dummy target (ValBase value) ;;
            mret tt
          end
        | _ => state_fail Internal
        end

      else state_fail Internal
    | _ => state_fail Internal
    end.

  Definition eval_builtin_func (name: P4String) (obj: ValueLvalue) (type_args : list P4Type) (args: list (option Expression)) : env_monad Value :=
    let name := P4String.str name in
    let* args' := eval_arguments args in
    if String.eqb name String.isValid
    then eval_is_valid obj
    else if String.eqb name String.setValid
    then dummy_value _ (eval_set_bool obj true)
    else if String.eqb name String.setInvalid
    then dummy_value _ (eval_set_bool obj false)
    else if String.eqb name String.pop_front
    then dummy_value _ (eval_pop_front obj args')
    else if String.eqb name String.push_front
    then dummy_value _ (eval_push_front obj args')
    else if is_packet_func name 
    then dummy_value _ (eval_packet_func obj name type_args args)
    else state_fail Internal.

  Definition eval_extern_func (name: String.t) (obj: ValueLvalue) (type_args: list P4Type) (args: list (option Expression)): env_monad Value.
  Admitted.
  (* TODO fix
  let* Packet bits := unpack_extern_obj (find_lvalue obj) in
  dummy_value (eval_packet_func obj name bits type_args args).
   *)

  Definition eval_method_call (func: Expression) (type_args: list P4Type) (args: list (option Expression)) : env_monad Value :=
    let* func' := eval_expression func in
    match func' with
    | ValObj (ValObjBuiltinFun name obj) => eval_builtin_func name obj type_args args
    (* | ValExternFun name caller params => eval_extern_func name obj type_args args *)
    | _ => state_fail Internal (* TODO: other function types *)
    end.

  Fixpoint eval_block (blk: Block) : env_monad unit :=
    match blk with
    | BlockEmpty _ =>
      mret tt
    | BlockCons stmt rest =>
      eval_statement stmt;;
      eval_block rest
    end
  with eval_statement (stmt: Statement) : env_monad unit :=
         let 'MkStatement _ stmt _ := stmt in
         match stmt with
         | StatMethodCall func type_args args =>
           state_fail Internal
         | StatAssignment lhs rhs =>
           let* lval := eval_lvalue lhs in
           let* val := eval_expression rhs in
           env_update _ tags_dummy lval val
         | StatBlock block =>
           stack_push _ ;;
           eval_block block ;;
           stack_pop _
         | StatConstant type name init =>
           env_insert _ name.(P4String.str) (ValBase init)
         | StatVariable type name init =>
           let* value :=
              match init with
              | None => mret (default_value type)
              | Some expr => eval_expression expr
              end in
           env_insert _ name.(P4String.str) value
         | StatInstantiation _ _ _ _
         | StatDirectApplication _ _
         | StatConditional _ _ _
         | StatExit
         | StatEmpty
         | StatReturn _
         | StatSwitch _ _ =>
           state_fail Internal
         end.

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
    | List.nil    => state_fail Internal
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
