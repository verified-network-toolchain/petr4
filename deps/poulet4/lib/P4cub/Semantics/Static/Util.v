From Coq Require Import PArith.BinPos ZArith.BinInt NArith.BinNat.
From Poulet4 Require Export P4cub.Semantics.Climate
     Utils.P4Arith P4cub.Syntax.Syntax.
Import String AllCubNotations.

(** Statement signals. *)
Variant signal : Set :=
| Cont   (** continue *)
| Return (** return *).

(** Least-upper bound on signals *)
Definition lub (sg1 sg2 : signal) : signal :=
  match sg1, sg2 with
  | Cont, _
  | _, Cont => Cont
  | _, _    => Return
  end.

(** Greatest-lower bound on signals. *)
Definition glb (sg1 sg2 : signal) : signal :=
  match sg1, sg2 with
  | Return, _
  | _, Return => Return
  | _, _ => Cont
  end.

(** Evidence for a type being a numeric of a given width. *)
Variant numeric_width : N -> Expr.t -> Prop :=
| numeric_width_bit : forall w, numeric_width w (Expr.TBit w)
| numeric_width_int : forall w, numeric_width (Npos w) (Expr.TInt w).

(** Evidence for a type being numeric. *)
Definition numeric (τ : Expr.t) : Prop := exists w, numeric_width w τ.

(** Evidence a unary operation is valid for a type. *)
Variant uop_type : Expr.uop -> Expr.t -> Expr.t -> Prop :=
  | UTBool :
    uop_type `!%uop Expr.TBool Expr.TBool
  | UTBitNot τ :
    numeric τ -> uop_type `~%uop τ τ
  | UTUMinus τ :
    numeric τ -> uop_type `-%uop τ τ
  | UTIsValid ts :
    uop_type Expr.IsValid (Expr.TStruct true ts) Expr.TBool
  | UTSetValidity b ts :
    uop_type (Expr.SetValidity b) (Expr.TStruct true ts) (Expr.TStruct true ts).

(** Evidence a binary operation is valid
    for operands of a type and produces some type. *)
Variant bop_type : Expr.bop -> Expr.t -> Expr.t -> Expr.t -> Prop :=
  | BTPlus τ : numeric τ -> bop_type `+%bop τ τ τ
  | BTPlusSat τ : numeric τ -> bop_type |+|%bop τ τ τ
  | BTMinus τ : numeric τ -> bop_type `-%bop τ τ τ
  | BTMinusSat τ : numeric τ -> bop_type |-|%bop τ τ τ
  | BTTimes τ : numeric τ -> bop_type ×%bop τ τ τ
  | BTShl τ1 w2 : numeric τ1 -> bop_type <<%bop τ1 (Expr.TBit w2) τ1
  | BTShr τ1 w2 : numeric τ1 -> bop_type >>%bop τ1 (Expr.TBit w2) τ1
  | BTBitAnd τ : numeric τ -> bop_type &%bop τ τ τ
  | BTBitXor τ : numeric τ -> bop_type ^%bop τ τ τ
  | BTBitOr τ : numeric τ -> bop_type Expr.BitOr τ τ τ
  | BTLe τ : numeric τ -> bop_type ≤%bop τ τ Expr.TBool
  | BTLt τ : numeric τ -> bop_type `<%bop τ τ Expr.TBool
  | BTGe τ : numeric τ -> bop_type ≥%bop τ τ Expr.TBool
  | BTGt τ : numeric τ -> bop_type `>%bop τ τ Expr.TBool
  | BTAnd : bop_type `&&%bop Expr.TBool Expr.TBool Expr.TBool
  | BTOr : bop_type `||%bop Expr.TBool Expr.TBool Expr.TBool
  | BTEq τ : bop_type `==%bop τ τ Expr.TBool
  | BTNotEq τ : bop_type !=%bop τ τ Expr.TBool
  | BTPlusPlusBit w1 w2 τ2 :
    numeric_width w2 τ2 ->
    bop_type `++%bop (Expr.TBit w1) τ2 (Expr.TBit (w1 + w2)%N)
  | BTPlusPlusInt w1 w2 τ2 :
    numeric_width (Npos w2) τ2 ->
    bop_type `++%bop (Expr.TInt w1) τ2 (Expr.TInt (w1 + w2)%positive)
  | BTPlusPlusIntZero w1 τ2 :
    numeric_width N0 τ2 ->
    bop_type `++%bop (Expr.TInt w1) τ2 (Expr.TInt w1).

(** Evidence a cast is proper. *)
Variant proper_cast : Expr.t -> Expr.t -> Prop :=
  | pc_bool_bit : proper_cast Expr.TBool (Expr.TBit 1)
  | pc_bit_bool : proper_cast (Expr.TBit 1) Expr.TBool
  | pc_bit_int w : proper_cast (Expr.TBit (Npos w)) (Expr.TInt w)
  | pc_int_bit w : proper_cast (Expr.TInt w) (Expr.TBit (Npos w))
  | pc_bit_bit w1 w2 : proper_cast (Expr.TBit w1) (Expr.TBit w2)
  | pc_int_int w1 w2 : proper_cast (Expr.TInt w1) (Expr.TInt w2)
  | pc_struct_hdr ts :
    proper_cast (Expr.TStruct true ts) (Expr.TStruct false ts).

(** Ok types. *)
Inductive t_ok (Δ : nat) : Expr.t -> Prop :=
| bool_ok :
  t_ok Δ Expr.TBool
| bit_ok w :
  t_ok Δ (Expr.TBit w)
| int_ok w :
  t_ok Δ (Expr.TInt w)
| error_ok :
  t_ok Δ Expr.TError
| array_ok n t :
  t_ok Δ t ->
  t_ok Δ (Expr.TArray n t)
| struct_ok b ts :
  Forall (t_ok Δ) ts ->
  t_ok Δ (Expr.TStruct b ts)
| var_ok T :
  (T < Δ)%nat ->
  t_ok Δ T.

Variant t_ok_lists (Δ : nat) : Expr.lists -> Prop :=
  | t_ok_lists_array τ :
    t_ok Δ τ -> t_ok_lists Δ (Expr.lists_array τ)
  | t_ok_lists_struct :
    t_ok_lists Δ Expr.lists_struct
  | t_ok_lists_header b :
    t_ok_lists Δ (Expr.lists_header b).

(** Function names to signatures. *)
Definition fenv : Set :=
  Clmt.t
    string (** function name. *)
    (nat (** type parameters. *)
     * Expr.arrowT (** signature. *)).

(** Action names to signatures. *)
Definition aenv : Set :=
  Clmt.t
    string (** action name. *)
    (list Expr.t (** control-plane parameters. *)
     * Expr.params (** data-plane parameters *)).

Variant instance_sig : Set :=
  | ParserSig
  | ControlSig.

(** Instance names to types. *)
Definition ienv : Set :=
  Clmt.t
    string (** Instance name *)
    (Field.fs
       string (** Method name. *)
       (nat * Expr.arrowT (** Method type signature. *))
     + instance_sig  (** Parser or control instance. *)
       * list string (** Types of extern arguments. *)
       * Expr.params (** Types of expression arguments. *)).

(** Available table names. *)
Definition tbl_env : Set := list string.

(** Statement context. *)
Variant ctx : Set :=
  | CAction (available_actions : aenv)
            (available_instances : ienv) (* action block *)
  | CFunction (return_type : option Expr.t)
  | CApplyBlock (tables : tbl_env)
                (available_actions : aenv)
                (available_instances : ienv) (* control apply block *)
  | CParserState
      (total_states : nat)
      (available_instances : ienv) (* parser state *).

(** Evidence an extern method call context is ok. *)
Variant extern_call_ok (eis : ienv) : ctx -> Prop :=
| extern_action_ok {aa} :
  extern_call_ok eis (CAction aa eis)
| extern_apply_block_ok {tbls} {aa} :
  extern_call_ok eis (CApplyBlock tbls aa eis)
| extern_parser_state_ok {ts} :
  extern_call_ok eis (CParserState ts eis).

(** Evidence an action call context is ok. *)
Variant action_call_ok
        (aa : aenv) : ctx -> Prop :=
  | action_action_ok {eis} :
    action_call_ok aa (CAction aa eis)
  | action_apply_block_ok {tbls} {eis} :
    action_call_ok aa (CApplyBlock tbls aa eis).

(** Evidence an exit context ok. *)
Variant exit_ctx_ok : ctx -> Prop :=
  | exit_action_ok {aa} {eis} :
    exit_ctx_ok (CAction aa eis)
  | exit_applyblk_ok {tbls} {aa} {eis} :
    exit_ctx_ok (CApplyBlock tbls aa eis).

(** Evidence a parser state transition is ok. *)
Variant transition_ok (total_states : nat) : ctx -> Prop :=
  | transition_parser_state_ok {i} :
    transition_ok total_states (CParserState total_states i).

(** Evidence a table invocation is ok. *)
Variant table_invoke_ok (tbls : tbl_env) : ctx -> Prop :=
  | table_invoke_applyblk_ok {aa} {i} :
    table_invoke_ok tbls (CApplyBlock tbls aa i).

(** Evidence applying an instance is ok. *)
Variant apply_instance_ok (i : ienv) : instance_sig -> ctx -> Prop :=
  | apply_control_applyblk_ok {tbls} {aa} :
    apply_instance_ok i ControlSig (CApplyBlock tbls aa i)
  | apply_parser_state_ok {ts} :
    apply_instance_ok i ParserSig (CParserState ts i).

(** Evidence a void return is ok. *)
Variant return_void_ok : ctx -> Prop :=
  | return_void_action {aa} {eis} :
    return_void_ok (CAction aa eis)
  | return_void_void :
    return_void_ok (CFunction None)
  | return_void_applyblk
      {tbls} {aa} {cis} :
    return_void_ok (CApplyBlock tbls aa cis).

(** Put parameters into environment. *)
Definition bind_all (ps : Expr.params) (Γ : list Expr.t) : list Expr.t :=
  map (fun 
       '(PAIn τ
        | PAOut τ
        | PAInOut τ) => τ) (map snd ps) ++ Γ.

(** Constructor Parameter types, for instantiations *)
Inductive constructor_type : Set :=
| ControlType
    (constructor_parameters : list TopDecl.it)
    (expr_constructor_params : list Expr.t)
    (extern_params : list string)
    (parameters : Expr.params) (** control types *)
| ParserType
    (constructor_parameters : list TopDecl.it)
    (expr_constructor_params : list Expr.t)
    (extern_params : list string)
    (parameters : Expr.params) (** parser types *)
| PackageType (** package types *)
    (constructor_parameters : list TopDecl.it)
    (expr_constructor_params : list Expr.t)
| ExternType (** extern types *)
    (type_params : nat)
    (constructor_parameters : list TopDecl.it)
    (expr_constructor_params : list Expr.t)
    (extern_name : string) (* TODO: methods? *).

(** Available constructor signatures. *)
Definition constructor_env : Set :=
  Clmt.t string constructor_type.

Import Clmt.Notations.
Open Scope climate_scope.

Definition insts_bind_externs ename methods insts : ienv :=
  ename ↦ inl methods ,, insts.

Definition insts_bind_other x sig ext_params params insts : ienv :=
    x ↦ inr (sig,ext_params,params) ,, insts.

(** Put (constructor) parameters
    into environments for typing
    control or parser declarations. *)
Definition cbind_all :
  ienv -> TopDecl.constructor_params -> ienv :=
  List.fold_right
    (fun '(x,it) i =>
       match it with
       | TopDecl.ControlInstType res pars
         => insts_bind_other x ControlSig res pars i
       | TopDecl.ParserInstType res pars
         => insts_bind_other x ParserSig res pars i
       | TopDecl.ExternInstType _ => i (* TODO *)
       | TopDecl.PackageInstType => i (* TODO *)
       end).

(** Valid parser states. *)
Variant valid_state (total : nat) : Parser.state_label -> Prop :=
  | start_valid :
    valid_state total Parser.Start
  | accept_valid :
    valid_state total Parser.Accept
  | reject_valid :
    valid_state total Parser.Reject
  | name_valid (st : nat) :
    (st < total)%nat ->
    valid_state total st.

(** Appropriate signal. *)
Variant good_signal : Expr.arrowT -> signal -> Prop :=
  | good_signal_cont params :
    good_signal {|paramargs:=params; rtrns:=None|} Cont
  | good_signal_return params ret :
    good_signal {|paramargs:=params; rtrns:=Some ret|} Return.

(** (Syntactic) Evidence an expression may be an lvalue. *)
Inductive lvalue_ok : Expr.e -> Prop :=
| lvalue_var τ og x :
  lvalue_ok (Expr.Var τ og x)
| lvalue_bit_slice e h l :
  lvalue_ok e ->
  lvalue_ok (Expr.Slice h l e)
| lvalue_index τ e₁ e₂ :
  lvalue_ok e₁ ->
  lvalue_ok (Expr.Index τ e₁ e₂)
| lvalue_member τ x e :
  lvalue_ok e ->
  lvalue_ok (Expr.Member τ x e).

Variant type_lists_ok
  : Expr.lists -> Expr.t -> list Expr.t -> Prop :=
  | type_array_ok w τ :
    type_lists_ok
      (Expr.lists_array τ)
      (Expr.TArray w τ)
      (List.repeat τ (N.to_nat w))
  | type_struct_ok τs :
    type_lists_ok
      Expr.lists_struct
      (Expr.TStruct false τs) τs
  | type_header_ok b τs :
    type_lists_ok
      (Expr.lists_header b)
      (Expr.TStruct true τs) τs.
