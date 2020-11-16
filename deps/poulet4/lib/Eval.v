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
  Context `{tags_inst: Tags}.

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
    | ValBit width bits => Some (ValBit width (bvector_negate bits))
    | ValInt width bits => Some (ValInt width (bvector_negate bits))
    | ValInteger n => Some (ValInteger (Z.opp n))
    | _ => None
    end.

  Definition bvec_of_z (width: nat) (z: Z) : (Bvector width).
  Admitted.

  Fixpoint eval_expression (expr: Expression) : env_monad Value :=
    let '(MkExpression _ expr _ _) := expr in
    match expr with
    | ExpBool value => mret (ValBool value)
    | ExpInt value =>
      match snd value with
      | Types.MkP4IntPreT value (Some (width, true)) =>
        mret (ValInt width (bvec_of_z width value))
      | Types.MkP4IntPreT value (Some (width, false)) =>
        mret (ValBit width (bvec_of_z width value))
      | Types.MkP4IntPreT value None =>
        mret (ValInteger value)
      end
    | ExpString value => mret (ValString (snd value))
    | ExpArrayAccess array index =>
      let* index' := unpack_inf_int (eval_expression index) in
      let* array' := unpack_array (eval_expression array) in
      lift_option (index_z_error array' index')
    | ExpBitStringAccess array hi lo =>
      state_fail Internal
    | ExpList exprs =>
      lift_monad ValTuple (sequence (List.map eval_expression exprs))
    | ExpRecord entries => 
      let actions := List.map eval_kv entries in
      lift_monad ValRecord (sequence actions)
    | ExpUnaryOp op arg => 
      match snd op with
      | Types.Not => 
        let* b := unpack_bool (eval_expression arg) in
        mret (ValBool (negb b))
      | Types.BitNot => 
        let* inner := eval_expression arg in
        match inner with
        | ValBit w bits => mret (ValBit w (Bneg w bits))
        | ValVarbit m w bits => mret (ValVarbit m w (Bneg w bits))
        | _ => state_fail Internal
        end
      | Types.UMinus =>
        let* inner := eval_expression arg in
        lift_option (eval_minus inner)
      end
    | _ => mret (ValBool false) (* TODO *)
    end

  with eval_kv (kv: KeyValue) : env_monad (string * Value) :=
         let '(MkKeyValue _ key expr) := kv in
         let* value := eval_expression expr in
         mret (snd key, value).

  Definition eval_is_valid (obj: ValueLvalue) : env_monad Value :=
    let* (_, valid) := unpack_header (find_lvalue obj) in
    mret (ValBool valid).

  Definition eval_set_bool (obj: ValueLvalue) (valid: bool) : env_monad unit :=
    let* (fields, _) := unpack_header (find_lvalue obj) in
    update_lvalue obj (ValHeader fields valid).

  Definition eval_pop_front (obj: ValueLvalue) (args: list (option Value)) : env_monad unit :=
    match args with
    | Some (ValInteger count) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack (find_lvalue obj) in
      let padding := ValHeader (MStr.Raw.empty _) false in
      let* elements' := lift_option (rotate_left_z elements count padding) in
      let next_index' := next_index - (Z.to_nat count) in
      let value' := ValStack elements' size next_index' in
      update_lvalue obj value'
    | _ => state_fail Internal
    end.

  Definition eval_push_front (obj: ValueLvalue) (args: list (option Value)) : env_monad unit :=
    match args with
    | Some (ValInteger count) :: nil => 
      let* '(elements, size, next_index) := unpack_header_stack (find_lvalue obj) in
      let padding := ValHeader (MStr.Raw.empty _) false in
      let* elements' := lift_option (rotate_right_z elements count padding) in
      let next_index' := min size (next_index + (Z.to_nat count)) in
      let value' := ValStack elements' size next_index' in
      update_lvalue obj value'
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

  Definition eval_builtin_func (name: string) (obj: ValueLvalue) (args: list (option Expression)) : env_monad Value :=
    let* args' := eval_arguments args in
    match name with
    | "isValid" => eval_is_valid obj
    | "setValid" => dummy_value (eval_set_bool obj true)
    | "setInvalid" => dummy_value (eval_set_bool obj false)
    | "pop_front" => dummy_value (eval_pop_front obj args')
    | "push_front" => dummy_value (eval_push_front obj args')
    | _ => state_fail Internal
    end.

  Definition eval_packet_func (obj: ValueLvalue) (name: string) (bits: list bool) (type_args: list P4Type) (args: list (option Expression)) : env_monad unit.
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

  Definition eval_extern_func (name: string) (obj: ValueLvalue) (type_args: list P4Type) (args: list (option Expression)): env_monad Value.
  Admitted.
  (* TODO fix
  let* Packet bits := unpack_extern_obj (find_lvalue obj) in
  dummy_value (eval_packet_func obj name bits type_args args).
   *)

  Definition eval_method_call (func: Expression) (type_args: list P4Type) (args: list (option Expression)) : env_monad Value :=
    let* func' := eval_expression func in
    match func' with
    | ValBuiltinFun name obj => eval_builtin_func name obj args
    (* | ValExternFun name caller params => eval_extern_func name obj type_args args *)
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
         | StatMethodCall func type_args args =>
           toss_value (eval_method_call func type_args args)
         | StatAssignment lhs rhs =>
           let* lval := eval_lvalue lhs in
           let* val := eval_expression rhs in
           update_lvalue lval val
         | StatBlock block =>
           map_env push_scope;;
           eval_block block;;
           lift_env_fn pop_scope
         | StatConstant _ type name init =>
           insert_environment (snd name) init
         | StatVariable _ type name init =>
           let* value :=
              match init with
              | None => mret (default_value type)
              | Some expr => eval_expression expr
              end
           in
           insert_environment (snd name) value
         | StatInstantiation _ _ _ _ _
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

  Fixpoint eval_cases (vals: list Value) (cases: list ParserCase) : env_monad string := 
    match cases with
    | List.nil    => state_fail Internal
    | MkParserCase _ matches next :: cases' => 
      let* passes := eval_match_expression vals matches in
      if passes then mret (snd next) else eval_cases vals cases'
    end.

  Definition eval_transition (t: ParserTransition) : env_monad string := 
    match t with
    | ParserDirect _ next =>
      mret (snd next)
    | ParserSelect _ exprs cases =>
      let* vs := sequence (List.map eval_expression exprs) in 
      eval_cases vs cases
    end.

End Eval.
