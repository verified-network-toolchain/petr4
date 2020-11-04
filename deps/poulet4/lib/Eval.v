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

Definition default_value (A: P4Type) : Value_value.
Admitted.

Definition eval_lvalue (expr: Expression) : env_monad Value_lvalue.
Admitted.

Definition bvector_negate {n: nat} (b: Bvector n) : Bvector n.
Admitted.

Definition bvector_add {n: nat} (x y: Bvector n) : Bvector n.
Admitted.

Definition eq_value (v1 v2: Value_value) : bool.
Admitted.

Definition eval_minus (v: Value_value) : option Value_value := 
  match v with
  | Val_Bit width bits => Some (Val_Bit width (bvector_negate bits))
  | Val_Int width bits => Some (Val_Int width (bvector_negate bits))
  | Val_Integer n => Some (Val_Integer (Z.opp n))
  | _ => None
  end.

Definition bvec_of_z (width: nat) (z: Z) : (Bvector width).
Admitted.

Fixpoint eval_expression (expr: Expression) : env_monad Value_value :=
  let '(MkExpression _ expr _ _) := expr in
  match expr with
  | Exp_Bool value => mret (Val_Bool value)
  | Exp_Int value =>
    match snd value with
    | Types.MkP4Int_pre_t value (Some (width, true)) =>
      mret (Val_Int width (bvec_of_z width value))
    | Types.MkP4Int_pre_t value (Some (width, false)) =>
      mret (Val_Bit width (bvec_of_z width value))
    | Types.MkP4Int_pre_t value None =>
      mret (Val_Integer value)
    end
  | Exp_String value => mret (Val_String (snd value))
  | Exp_ArrayAccess array index =>
    let* index' := unpack_inf_int (eval_expression index) in
    let* array' := unpack_array (eval_expression array) in
    lift_option (index_z_error array' index')
  | Exp_BitStringAccess array hi lo =>
    state_fail Internal
  | Exp_List exprs =>
    lift_monad Val_Tuple (sequence (List.map eval_expression exprs))
  | Exp_Record entries => 
    let actions := List.map eval_kv entries in
    lift_monad Val_Record (sequence actions)
  | Exp_UnaryOp op arg => 
    match snd op with
    | Types.Not => 
      let* b := unpack_bool (eval_expression arg) in
      mret (Val_Bool (negb b))
    | Types.BitNot => 
      let* inner := eval_expression arg in
      match inner with
      | Val_Bit w bits => mret (Val_Bit w (Bneg w bits))
      | Val_Varbit m w bits => mret (Val_Varbit m w (Bneg w bits))
      | _ => state_fail Internal
      end
    | Types.UMinus =>
      let* inner := eval_expression arg in
      lift_option (eval_minus inner)
    end
  | _ => mret (Val_Bool false) (* TODO *)
  end

with eval_kv (kv: KeyValue) : env_monad (string * Value_value) :=
  let '(MkKeyValue _ key expr) := kv in
  let* value := eval_expression expr in
  mret (snd key, value).

Definition eval_is_valid (obj: Value_lvalue) : env_monad Value_value :=
  let* (_, valid) := unpack_header (find_lvalue obj) in
  mret (Val_Bool valid).

Definition eval_set_bool (obj: Value_lvalue) (valid: bool) : env_monad unit :=
  let* (fields, _) := unpack_header (find_lvalue obj) in
  update_lvalue obj (Val_Header fields valid).

Definition eval_pop_front (obj: Value_lvalue) (args: list (option Value_value)) : env_monad unit :=
  match args with
  | Some (Val_Integer count) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack (find_lvalue obj) in
      let padding := Val_Header (MStr.Raw.empty _) false in
      let* elements' := lift_option (rotate_left_z elements count padding) in
      let next_index' := next_index - (Z.to_nat count) in
      let value' := Val_Stack elements' size next_index' in
      update_lvalue obj value'
  | _ => state_fail Internal
  end.

Definition eval_push_front (obj: Value_lvalue) (args: list (option Value_value)) : env_monad unit :=
  match args with
  | Some (Val_Integer count) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack (find_lvalue obj) in
      let padding := Val_Header (MStr.Raw.empty _) false in
      let* elements' := lift_option (rotate_right_z elements count padding) in
      let next_index' := min size (next_index + (Z.to_nat count)) in
      let value' := Val_Stack elements' size next_index' in
      update_lvalue obj value'
  | _ => state_fail Internal
  end.

Fixpoint eval_arguments (args: list (option Expression)) : env_monad (list (option Value_value)) :=
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

Definition eval_builtin_func (name: string) (obj: Value_lvalue) (args: list (option Expression)) : env_monad Value_value :=
  let* args' := eval_arguments args in
  match name with
  | "isValid" => eval_is_valid obj
  | "setValid" => dummy_value (eval_set_bool obj true)
  | "setInvalid" => dummy_value (eval_set_bool obj false)
  | "pop_front" => dummy_value (eval_pop_front obj args')
  | "push_front" => dummy_value (eval_push_front obj args')
  | _ => state_fail Internal
  end.

Definition eval_packet_func (obj: Value_lvalue) (name: string) (bits: list bool) (type_args: list P4Type) (args: list (option Expression)) : env_monad unit.
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
        update_lvalue obj (Val_ExternObj (Packet bits')) ;;
        state_fail error
      | (inl value, bits') =>
        update_lvalue obj (Val_ExternObj (Packet bits')) ;;
        update_lvalue target value ;;
        mret tt
      end
    | _ => state_fail Internal
    end
  | _ => state_fail Internal
  end.
*)

Definition eval_extern_func (name: string) (obj: Value_lvalue) (type_args: list P4Type) (args: list (option Expression)): env_monad Value_value.
Admitted.
(* TODO fix
  let* Packet bits := unpack_extern_obj (find_lvalue obj) in
  dummy_value (eval_packet_func obj name bits type_args args).
*)

Definition eval_method_call (func: Expression) (type_args: list P4Type) (args: list (option Expression)) : env_monad Value_value :=
  let* func' := eval_expression func in
  match func' with
  | Val_BuiltinFun name obj => eval_builtin_func name obj args
  (* | Val_ExternFun name caller params => eval_extern_func name obj type_args args *)
  | _ => state_fail Internal (* TODO: other function types *)
  end.

Fixpoint eval_block (blk: Block) : env_monad unit :=
  match blk with
  | BlockEmpty _ _ =>
    mret tt
  | BlockCons stmt rest =>
    eval_statement stmt;;
    eval_block rest
  end

with eval_statement (stmt: Statement) : env_monad unit :=
  let 'MkStatement _ stmt _ := stmt in
  match stmt with
  | Stat_MethodCall func type_args args =>
    toss_value (eval_method_call func type_args args)
  | Stat_Assignment lhs rhs =>
    let* lval := eval_lvalue lhs in
    let* val := eval_expression rhs in
    update_lvalue lval val
  | Stat_BlockStatement block =>
    map_env push_scope;;
    eval_block block;;
    lift_env_fn pop_scope
  | Stat_Constant _ _ type name init =>
    insert_environment (snd name) init
  | Stat_Variable _ _ type name init =>
    let* value :=
       match init with
       | None => mret (default_value type)
       | Some expr => eval_expression expr
       end
    in
    insert_environment (snd name) value
  | Stat_DirectApplication _ _
  | Stat_Conditional _ _ _
  | Stat_Exit
  | Stat_EmptyStatement
  | Stat_Return _
  | Stat_Switch _ _ =>
    state_fail Internal
  end.

  (* TODO: sophisticated pattern matching for the match expression as needed *)
Fixpoint eval_match_expression (vals: list Value_value) (matches: list Match) : env_monad bool :=
  match (vals, matches) with
  | (List.nil, List.nil) => mret true
  | (v :: vals', MkMatch _ m _ :: matches') => 
    match m with
    | Match_DontCare => eval_match_expression vals' matches'
    | Match_Expression e => 
      let* v' := eval_expression e in 
        if eq_value v v' then eval_match_expression vals' matches' else mret false
    end
  | _ => mret false
  end.

Fixpoint eval_cases (vals: list Value_value) (cases: list Parser_case) : env_monad string := 
  match cases with
  | List.nil    => state_fail Internal
  | MkParser_case _ matches next :: cases' => 
    let* passes := eval_match_expression vals matches in
    if passes then mret (snd next) else eval_cases vals cases'
  end.

Definition eval_transition (t: Parser_transition) : env_monad string := 
  match t with
  | Parse_Direct _ next =>
    mret (snd next)
  | Parse_Select _ exprs cases =>
    let* vs := sequence (List.map eval_expression exprs) in 
    eval_cases vs cases
  end.
