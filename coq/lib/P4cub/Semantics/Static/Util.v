From Coq Require Import PArith.BinPos ZArith.BinInt NArith.BinNat.
From Poulet4 Require Export P4cub.Semantics.Climate
     Utils.P4Arith P4cub.Syntax.Syntax.

(** Statement signals. *)
Module Signal.
  Variant t : Set :=
    | Cnt  (** continue *)
    | Ext  (** exit *)
    | Ret  (** return *)
    | Trns (** transition *).

  (** Least-upper bound on signals *)
  Definition lub (sg1 sg2 : t) : option t :=
    match sg1, sg2 with
    | Cnt, _
    | _, Cnt => Some Cnt
    | Trns, (Ext | Trns)
    | Ext, Trns => Some Trns
    | Ret, (Ext | Ret)
    | Ext, Ret => Some Ret
    | Ext, Ext => Some Ext
    | Trns, Ret
  | Ret, Trns => None
    end.
End Signal.

(** Evidence for a type being a numeric of a given width. *)
Variant numeric_width : N -> Typ.t -> Prop :=
| numeric_width_bit : forall w, numeric_width w (Typ.Bit w)
| numeric_width_int : forall w, numeric_width (Npos w) (Typ.Int w).

(** Evidence for a type being numeric. *)
Definition numeric (τ : Typ.t) : Prop := exists w, numeric_width w τ.

(** Evidence a unary operation is valid for a type. *)
Variant una_type : Una.t -> Typ.t -> Typ.t -> Prop :=
  | una_Bool :
    una_type `!%una Typ.Bool Typ.Bool
  | una_BitNot τ :
    numeric τ -> una_type `~%una τ τ
  | una_UMinus τ :
    numeric τ -> una_type `-%una τ τ
  | una_IsValid ts :
    una_type Una.IsValid (Typ.Struct true ts) Typ.Bool.

(** Evidence a binary operation is valid
    for operands of a type and produces some type. *)
Variant bin_type : Bin.t -> Typ.t -> Typ.t -> Typ.t -> Prop :=
  | bin_Plus τ : numeric τ -> bin_type `+%bin τ τ τ
  | bin_PlusSat τ : numeric τ -> bin_type |+|%bin τ τ τ
  | bin_Minus τ : numeric τ -> bin_type `-%bin τ τ τ
  | bin_MinusSat τ : numeric τ -> bin_type |-|%bin τ τ τ
  | bin_Times τ : numeric τ -> bin_type ×%bin τ τ τ
  | bin_Shl τ1 w2 : numeric τ1 -> bin_type <<%bin τ1 (Typ.Bit w2) τ1
  | bin_Shr τ1 w2 : numeric τ1 -> bin_type >>%bin τ1 (Typ.Bit w2) τ1
  | bin_BitAnd τ : numeric τ -> bin_type &%bin τ τ τ
  | bin_BitXor τ : numeric τ -> bin_type ^%bin τ τ τ
  | bin_BitOr τ : numeric τ -> bin_type Bin.BitOr τ τ τ
  | bin_Le τ : numeric τ -> bin_type ≤%bin τ τ Typ.Bool
  | bin_Lt τ : numeric τ -> bin_type `<%bin τ τ Typ.Bool
  | bin_Ge τ : numeric τ -> bin_type ≥%bin τ τ Typ.Bool
  | bin_Gt τ : numeric τ -> bin_type `>%bin τ τ Typ.Bool
  | bin_And : bin_type `&&%bin Typ.Bool Typ.Bool Typ.Bool
  | bin_Or : bin_type `||%bin Typ.Bool Typ.Bool Typ.Bool
  | bin_Eq τ : bin_type `==%bin τ τ Typ.Bool
  | bin_NotEq τ : bin_type !=%bin τ τ Typ.Bool
  | bin_PlusPlusBit w1 w2 τ2 :
    numeric_width w2 τ2 ->
    bin_type `++%bin (Typ.Bit w1) τ2 (Typ.Bit (w1 + w2)%N)
  | bin_PlusPlusInt w1 w2 τ2 :
    numeric_width (Npos w2) τ2 ->
    bin_type `++%bin (Typ.Int w1) τ2 (Typ.Int (w1 + w2)%positive)
  | bin_PlusPlusIntZero w1 τ2 :
    numeric_width N0 τ2 ->
    bin_type `++%bin (Typ.Int w1) τ2 (Typ.Int w1).

(** Evidence a cast is proper. *)
Variant proper_cast : Typ.t -> Typ.t -> Prop :=
  | pc_bool_bit : proper_cast Typ.Bool (Typ.Bit 1)
  | pc_bit_bool : proper_cast (Typ.Bit 1) Typ.Bool
  | pc_bit_int w : proper_cast (Typ.Bit (Npos w)) (Typ.Int w)
  | pc_int_bit w : proper_cast (Typ.Int w) (Typ.Bit (Npos w))
  | pc_bit_bit w1 w2 : proper_cast (Typ.Bit w1) (Typ.Bit w2)
  | pc_int_int w1 w2 : proper_cast (Typ.Int w1) (Typ.Int w2)
  | pc_struct_hdr ts :
    proper_cast (Typ.Struct true ts) (Typ.Struct false ts).

(** Ok types. *)
Inductive typ_ok (Δ : nat) : Typ.t -> Prop :=
| bool_ok :
  typ_ok Δ Typ.Bool
| bityp_ok w :
  typ_ok Δ (Typ.Bit w)
| intyp_ok w :
  typ_ok Δ (Typ.Int w)
| varbityp_ok w :
  typ_ok Δ (Typ.VarBit w)
| error_ok :
  typ_ok Δ Typ.Error
| array_ok n t :
  typ_ok Δ t ->
  typ_ok Δ (Typ.Array n t)
| structyp_ok b ts :
  Forall (typ_ok Δ) ts ->
  typ_ok Δ (Typ.Struct b ts)
| var_ok T :
  (T < Δ)%nat ->
  typ_ok Δ (Typ.Var T).

Variant typ_ok_lists (Δ : nat) : Lst.t -> Prop :=
  | typ_ok_lists_array τ :
    typ_ok Δ τ -> typ_ok_lists Δ (Lst.Array τ)
  | typ_ok_lists_struct :
    typ_ok_lists Δ Lst.Struct
  | typ_ok_lists_header b :
    typ_ok_lists Δ (Lst.Header b).

(** Function names to signatures. *)
Definition fenv : Set :=
  Clmt.t
    String.string (** function name. *)
    (nat (** type parameters. *)
     * Typ.arrowT (** signature. *)).

(** Action names to signatures. *)
Definition aenv : Set :=
  Clmt.t
    String.string (** action name. *)
    (list Typ.t (** control-plane parameters. *)
     * Typ.params (** data-plane parameters *)).

(** Instance names to types. *)
Definition ienv : Set :=
  Clmt.t
    String.string (** Instance name *)
    (Field.fs
       String.string (** Method name. *)
       (nat * Typ.arrowT (** Method type signature. *))
     + Cnstr.t (** Parser or control instance. *)
       * list String.string (** Types of extern arguments. *)
       * Typ.params (** Types of expression arguments. *)).

(** Available table names. *)
Definition tbl_env : Set :=
  Clmt.t
    String.string (** table name *)
    nat      (** number of actions *).

(** Statement context. *)
Variant ctx : Set :=
  | CAction (available_actions : aenv)
            (available_instances : ienv) (* action block *)
  | CFunction (return_type : option Typ.t)
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

(** Evidence applying an instance is ok. *)
Variant apply_instance_ok (i : ienv) : Cnstr.t -> ctx -> Prop :=
  | apply_control_applyblk_ok {tbls} {aa} :
    apply_instance_ok i Cnstr.Control (CApplyBlock tbls aa i)
  | apply_parser_state_ok {ts} :
    apply_instance_ok i Cnstr.Parser (CParserState ts i).

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
Definition bind_all (ps : Typ.params) (Γ : list Typ.t) : list Typ.t :=
  map (fun 
       '(PAIn τ
        | PAOut τ
        | PAInOut τ) => τ) (map snd ps) ++ Γ.

(** Constructor Parameter types, for instantiations *)
Inductive constructor_type : Set :=
| CtrType
    (flag : Cnstr.t)
    (constructor_parameters : list InstTyp.t)
    (expr_constructor_params : list Typ.t)
    (extern_params : list String.string)
    (parameters : Typ.params) (** control types *)
| PackageType (** package types *)
    (constructor_parameters : list InstTyp.t)
    (expr_constructor_params : list Typ.t)
| ExternType (** extern types *)
    (type_params : nat)
    (constructor_parameters : list InstTyp.t)
    (expr_constructor_params : list Typ.t)
    (extern_name : String.string) (* TODO: methods? *).

(** Available constructor signatures. *)
Definition constructor_env : Set :=
  Clmt.t String.string constructor_type.

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
  ienv -> Top.constructor_params -> ienv :=
  List.fold_right
    (fun '(x,it) i =>
       match it with
       | InstTyp.Ctr flag res pars
         => insts_bind_other x flag res pars i
       | InstTyp.Extern _ => i (* TODO *)
       | InstTyp.Package => i (* TODO *)
       end).

(** Valid parser states. *)
Variant valid_state (total : nat) : Lbl.t -> Prop :=
  | start_valid :
    valid_state total Lbl.Start
  | accept_valid :
    valid_state total Lbl.Accept
  | reject_valid :
    valid_state total Lbl.Reject
  | name_valid (st : nat) :
    (st < total)%nat ->
    valid_state total (Lbl.Name st).

(** Appropriate signal. *)
Variant good_signal : Typ.arrowT -> Signal.t -> Prop :=
  | good_signal_cont params :
    good_signal {|paramargs:=params; rtrns:=None|} Signal.Cnt
  | good_signal_return params ret :
    good_signal {|paramargs:=params; rtrns:=Some ret|} Signal.Ret.

(** (Syntactic) Evidence an expression may be an lvalue. *)
Inductive lexpr_ok : Exp.t -> Prop :=
| lexpr_var τ og x :
  lexpr_ok (Exp.Var τ og x)
| lexpr_bit_slice e h l :
  lexpr_ok e ->
  lexpr_ok (Exp.Slice h l e)
| lexpr_index τ e₁ e₂ :
  lexpr_ok e₁ ->
  lexpr_ok (Exp.Index τ e₁ e₂)
| lexpr_member τ x e :
  lexpr_ok e ->
  lexpr_ok (Exp.Member τ x e).

Variant type_lst_ok
  : Lst.t -> Typ.t -> list Typ.t -> Prop :=
  | type_array_ok w τ :
    type_lst_ok
      (Lst.Array τ)
      (Typ.Array w τ)
      (List.repeat τ (N.to_nat w))
  | type_struct_ok τs :
    type_lst_ok
      Lst.Struct
      (Typ.Struct false τs) τs
  | type_header_ok b τs :
    type_lst_ok
      (Lst.Header b)
      (Typ.Struct true τs) τs.
