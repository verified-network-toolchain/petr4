Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Strings.String.

Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Monads.State.

Require Import Value.
Require Import Environment.
Require Import Syntax.
Require Import Utils.
Require Import Unpack.

Require Import Platform.Packet.


Open Scope monad.

Definition default_value (A: type) : value.
Admitted.

Definition eval_lvalue (expr: expression) : env_monad lvalue.
Admitted.

Definition eval_minus (v: value) : option value := 
  match v with
  | ValFixedBit width bits => Some (ValFixedInt width (Z.sub (pow_two width) (of_bvector bits)))
  | ValFixedInt width value => Some (ValFixedInt width (Z.sub (pow_two width) value))
  | ValInfInt n => Some (ValInfInt (Z.opp n))
  | _ => None
  end.

Fixpoint eval_expression (expr: expression) : env_monad value :=
  match expr with
  | BoolExpression value => mret (ValBool value)
  | IntExpression value => mret (ValInfInt value)
  | StringExpression value => mret (ValString value)
  | ArrayAccess array index =>
    let* index' := unpack_inf_int (eval_expression index) in
    let* array' := unpack_array (eval_expression array) in
    lift_option (index_z_error array' index')
  | BitStringAccess array hi lo =>
    let* array' := unpack_array (eval_expression array) in
    let* hi'    := unpack_inf_int (eval_expression hi) in
    let* lo'    := unpack_inf_int (eval_expression lo) in
    lift_option (option_map ValArray (list_slice_z array' lo' hi'))
  | List exprs =>
    lift_monad ValArray (sequence (List.map eval_expression exprs))
  | Record entries => 
    let actions := List.map (fun x => match x with | MkKeyValue k e => v <- eval_expression e ;; mret (k, v) end) entries in
    lift_monad ValRecord (sequence actions)
  | UnaryOp op arg => 
    match op with
    | Not => 
      let* b := unpack_bool (eval_expression arg) in
      mret (ValBool (negb b))
    | BitNot => 
      let* inner := eval_expression arg in
      match inner with
      | ValFixedBit w bits => mret (ValFixedBit w (Bneg w bits))
      | ValVarBit w bits => mret (ValVarBit w (Bneg w bits))
      | _ => state_fail Internal
      end
    | BitMinus =>
      let* inner := eval_expression arg in
      lift_option (eval_minus inner)
    end
  | _ => mret (ValBool false) (* TODO *)
  end.

Definition eval_is_valid (obj: lvalue) : env_monad value :=
  let* hdr := unpack_header (find_lvalue obj) in
  let (valid, _) := hdr in
  mret (ValBool valid).

Definition eval_set_bool (obj: lvalue) (valid: bool) : env_monad unit :=
  let* hdr := unpack_header (find_lvalue obj) in
  match hdr with
  | MkHeader _ fields =>
    update_lvalue obj (ValHeader (MkHeader valid fields))
  end.

Definition eval_pop_front (obj: lvalue) (args: list (option value)) : env_monad unit :=
  match args with
  | Some (ValInfInt count) :: nil => 
      let* hdrstack := unpack_header_stack (find_lvalue obj) in
      let '(size, next_index, elements) := hdrstack in
      let padding := MkHeader false (MStr.Raw.empty _) in
      let* elements' := lift_option (rotate_left_z elements count padding) in
      let next_index' := next_index - (Z.to_nat count) in
      let value' := ValHeaderStack size next_index' elements' in
      update_lvalue obj value'
  | _ => state_fail Internal
  end.

Definition eval_push_front (obj: lvalue) (args: list (option value)) : env_monad unit :=
  match args with
  | Some (ValInfInt count) :: nil => 
      let* hdrstack := unpack_header_stack (find_lvalue obj) in
      let '(size, next_index, elements) := hdrstack in
      let padding := MkHeader false (MStr.Raw.empty _) in
      let* elements' := lift_option (rotate_right_z elements count padding) in
      let next_index' := min size (next_index + (Z.to_nat count)) in
      let value' := ValHeaderStack size next_index' elements' in
      update_lvalue obj value'
  | _ => state_fail Internal
  end.

Fixpoint eval_arguments (args: list (option expression)) : env_monad (list (option value)) :=
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

Definition eval_builtin_func (name: string) (obj: lvalue) (args: list (option expression)) : env_monad value :=
  let* args' := eval_arguments args in
  match name with
  | "isValid" => eval_is_valid obj
  | "setValid" => dummy_value (eval_set_bool obj true)
  | "setInvalid" => dummy_value (eval_set_bool obj false)
  | "pop_front" => dummy_value (eval_pop_front obj args')
  | "push_front" => dummy_value (eval_push_front obj args')
  | _ => state_fail Internal
  end.

Definition eval_packet_func (obj: lvalue) (name: string) (bits: list bool) (args: list (option expression)) : env_monad unit :=
  match name with
  | "extract" =>
    match args with
    | (Some target_expr) :: nil =>
      let* target := eval_lvalue target_expr in
      let* value := find_lvalue target in
      match eval_packet_extract_fixed value bits with
      | (inr error, bits') =>
        update_lvalue obj (ValExternObj (Packet bits')) ;;
        state_fail error
      | (inl value', bits') =>
        update_lvalue obj (ValExternObj (Packet bits')) ;;
        update_lvalue target value' ;;
        mret tt
      end
    | _ => state_fail Internal
    end
  | _ => state_fail Internal
  end.

Definition eval_extern_func (name: string) (obj: lvalue) (args: list (option expression)): env_monad value :=
  let* ext := unpack_extern_obj (find_lvalue obj) in
  match ext with
  | Packet bits => dummy_value (eval_packet_func obj name bits args)
  end.

Definition eval_method_call (func: expression) (type_args: list type) (args: list (option expression)) : env_monad value :=
  let* func' := eval_expression func in
  match func' with
  | ValBuiltinFunc name obj => eval_builtin_func name obj args
  | ValExternFunc name obj => eval_extern_func name obj args
  | _ => state_fail Internal (* TODO: other function types *)
  end.

Fixpoint eval_block (blk: block) : env_monad unit :=
  match blk with
  | BlockCons stmt rest =>
    eval_statement stmt;;
    eval_block rest
  | BlockEmpty => mret tt
  end

with eval_statement (stmt: statement) : env_monad unit :=
  match stmt with
  | MethodCall func type_args args =>
    toss_value (eval_method_call func type_args args)
  | Assignment lhs rhs =>
    let* lval := eval_lvalue lhs in
    let* val := eval_expression rhs in
    update_lvalue lval val
  | BlockStatement block =>
    map_env push_scope;;
    eval_block block;;
    lift_env_fn pop_scope
  | StatementConstant type name init =>
    let* value := eval_expression init in
    insert_environment name value
  | StatementVariable type name init =>
    let* value :=
       match init with
       | None => mret (default_value type)
       | Some expr => eval_expression expr
       end
    in
    insert_environment name value
  end.

  (* TODO: sophisticated pattern matching for the match expression as needed *)
Fixpoint eval_match_expression (vals: list value) (matches: list match_expression) : env_monad bool :=
  match (vals, matches) with
  | (List.nil, List.nil) => mret true
  | (v :: vals', m :: matches') => 
    match m with
    | DontCare          => eval_match_expression vals' matches'
    | MatchExpression e => 
      let* v' := eval_expression e in 
        if eq_value v v' then eval_match_expression vals' matches' else mret false
    end
  | _ => mret false
  end.

Fixpoint eval_cases (vals: list value) (cases: list Case.case) : env_monad string := 
  match cases with
  | List.nil    => state_fail Internal
  | c :: cases' => 
    let* passes := eval_match_expression vals (Case.matches c) in
      if passes then mret (Case.next c) else eval_cases vals cases'
  end.


Definition eval_transition (t: Transition.transition) : env_monad string := 
  let* vs := sequence (List.map eval_expression (Transition.exprs t)) in 
    eval_cases vs (Transition.cases t).

