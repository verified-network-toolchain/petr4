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

(** Evidence for a type being a numeric of a given width. *)
Variant numeric_width : N -> Expr.t -> Prop :=
| numeric_width_bit : forall w, numeric_width w (Expr.TBit w)
| numeric_width_int : forall w, numeric_width w (Expr.TInt w).

Ltac inv_numeric_width :=
  match goal with
  | H: numeric_width _ _ |- _ => inv H
  end.

(** Evidence for a type being numeric. *)
Definition numeric (τ : Expr.t) : Prop := exists w, numeric_width w τ.

Ltac inv_numeric :=
  match goal with
  | H: numeric _ |- _ => inv H; try inv_numeric_width
  end.

(** Evidence a unary operation is valid for a type. *)
Variant uop_type : Expr.uop -> Expr.t -> Expr.t -> Prop :=
  | UTBool :
    uop_type `!%uop Expr.TBool Expr.TBool
  | UTBitNot τ :
    numeric τ -> uop_type `~%uop τ τ
  | UTUMinus τ :
    numeric τ -> uop_type `-%uop τ τ
  | UTIsValid ts :
    uop_type Expr.IsValid (Expr.TStruct ts true) Expr.TBool
  | UTSetValidity b ts :
    uop_type (Expr.SetValidity b) (Expr.TStruct ts true) (Expr.TStruct ts true).

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
| BTPlusPlusBit w1 w2 w τ2 :
    (w1 + w2)%N = w ->
    numeric_width w2 τ2 ->
    bop_type `++%bop (Expr.TBit w1) τ2 (Expr.TBit w)
| BTPlusPlusInt w1 w2 w τ2 :
    (w1 + w2)%N = w ->
    numeric_width w2 τ2 ->
    bop_type `++%bop (Expr.TInt w1) τ2 (Expr.TInt w)
| BTPlusPlusIntZero w1 τ2 :
    numeric_width N0 τ2 ->
    bop_type `++%bop (Expr.TInt w1) τ2 (Expr.TInt w1).

(** Evidence a cast is proper. *)
Variant proper_cast : Expr.t -> Expr.t -> Prop :=
  | pc_bool_bit : proper_cast Expr.TBool (Expr.TBit 1)
  | pc_bit_bool : proper_cast (Expr.TBit 1) Expr.TBool
  | pc_bit_int w : proper_cast (Expr.TBit w) (Expr.TInt w)
  | pc_int_bit w : proper_cast (Expr.TInt w) (Expr.TBit w)
  | pc_bit_bit w1 w2 : proper_cast (Expr.TBit w1) (Expr.TBit w2)
  | pc_int_int w1 w2 : proper_cast (Expr.TInt w1) (Expr.TInt w2)
  | pc_tuple_hdr ts :
    Forall ProperType.proper_inside_header ts ->
    proper_cast (Expr.TStruct ts false) (Expr.TStruct ts true).

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
| struct_ok ts b :
  Forall (t_ok Δ) ts ->
  t_ok Δ (Expr.TStruct ts b)
| var_ok T :
  (T < Δ)%nat ->
  t_ok Δ T.

(*Import Clmt.Notations.*)

(** Function names to signatures. *)
Definition fenv : Set :=
  Clmt.t
    string (** function name. *)
    (nat (** type parameters. *)
     * Expr.arrowT (** signature. *)).

(** Action names to signatures. *)
Definition aenv : Set := Clmt.t string Expr.params.

(** de Bruijn environment of instance type signatures. *)
Definition ienv : Set :=
  list
    (list string (** Types of extern arguments. *)
     * Expr.params (** Types of expression arguments. *)).

(** De Bruijn environment of extern instance type signatures. *)
Definition eienv : Set :=
  list (Field.fs
          string (** Method name. *)
          (nat * Expr.arrowT (** Method type signature. *))).

(** Statement context. *)
Variant ctx : Set :=
  | CAction (available_actions : aenv)
            (available_externs : eienv) (* action block *)
  | CFunction (return_type : option Expr.t)
  | CApplyBlock (tables : list string)
                (available_actions : aenv)
                (available_controls : ienv)
                (available_externs : eienv) (* control apply block *)
  | CParserState (available_parsers : ienv)
                 (available_externs : eienv) (* parser state *).

(** Evidence an extern method call context is ok. *)
Variant extern_call_ok (eis : eienv) : ctx -> Prop :=
| extern_action_ok {aa : aenv} :
  extern_call_ok eis (CAction aa eis)
| extern_apply_block_ok {tbls : list string} {aa : aenv} {cis : ienv} :
  extern_call_ok eis (CApplyBlock tbls aa cis eis)
| extern_parser_state_ok {pis : ienv} :
  extern_call_ok eis (CParserState pis eis).
(**[]*)

(** Evidence an action call context is ok. *)
Variant action_call_ok
          (aa : aenv) : ctx -> Prop :=
| action_action_ok {eis : eienv} :
    action_call_ok aa (CAction aa eis)
| action_apply_block_ok {tbls : list string} {cis : ienv} {eis : eienv} :
    action_call_ok aa (CApplyBlock tbls aa cis eis).
(**[]*)

(** Evidence an exit context ok. *)
Variant exit_ctx_ok : ctx -> Prop :=
| exit_action_ok {aa : aenv} {eis : eienv} :
    exit_ctx_ok (CAction aa eis)
| exit_applyblk_ok {tbls : list string} {aa : aenv}
                   {cis : ienv} {eis : eienv} :
    exit_ctx_ok (CApplyBlock tbls aa cis eis).
(**[]*)

(** Evidence a void return is ok. *)
Variant return_void_ok : ctx -> Prop :=
| return_void_action {aa : aenv} {eis : eienv} :
    return_void_ok (CAction aa eis)
| return_void_void :
  return_void_ok (CFunction None)
| return_void_applyblk {tbls : list string} {aa : aenv}
                       {cis : ienv} {eis : eienv} :
    return_void_ok (CApplyBlock tbls aa cis eis).
(**[]*)

(** Put parameters into environment. *)
Definition bind_all (ps : Expr.params) (Γ : list Expr.t) : list Expr.t :=
  map (fun 
       '(PADirLess τ
        | PAIn τ
        | PAOut τ
        | PAInOut τ) => τ) ps ++ Γ.

(** Constructor Parameter types, for instantiations *)
Inductive constructor_type : Set :=
| ControlType
    (constructor_parameters : list TopDecl.it)
    (extern_params : list string)
    (parameters : Expr.params) (** control types *)
| ParserType
    (constructor_parameters : list TopDecl.it)
    (extern_params : list string)
    (parameters : Expr.params) (** parser types *)
| PackageType (** package types *)
    (constructor_parameters : list TopDecl.it)
| ExternType (** extern types *)
    (type_params : nat)
    (constructor_parameters : list TopDecl.it)
    (extern_name : string) (* TODO: methods? *).

(** Available constructor signatures. *)
Definition constructor_env : Set :=
  Clmt.t string constructor_type.

Import Clmt.Notations.
Open Scope climate_scope.

Record insts_env : Set :=
  {parsers:ienv; controls:ienv; externs:eienv}.

(** Put (constructor) parameters
    into environments for typing
    control or parser declarations. *)
Definition cbind_all (ie : insts_env) :
  TopDecl.constructor_params ->
  list Expr.t * insts_env :=
  List.fold_right
    (fun it '((Γ, {|parsers:=ps;controls:=cs;externs:=exts|} as i)) =>
       match it with
       | TopDecl.EType τ => (τ :: Γ , i)
       | TopDecl.ControlInstType res pars
         => (Γ, {|controls:=(res,pars)::cs;parsers:=ps;externs:=exts|})
       | TopDecl.ParserInstType res pars
         => (Γ, {|parsers:=(res,pars)::ps;controls:=ps;externs:=exts|})
       | TopDecl.ExternInstType _ => (Γ, i) (* TODO *)
       | TopDecl.PackageInstType => (Γ, i)
       end) ([], ie).

(** Valid parser states. *)
Variant valid_state (total : nat) : Parser.state -> Prop :=
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
| lvalue_var x τ :
  lvalue_ok (Expr.Var τ x)
| lvalue_bit_slice e h l :
  lvalue_ok e ->
  lvalue_ok (Expr.Slice e h l)
| lvalue_member τ x e :
  lvalue_ok e ->
  lvalue_ok (Expr.Member τ x e).

Fixpoint gen_tsub (τs : list Expr.t) (X : nat) : Expr.t :=
  match τs, X with
  | τ :: _, O => τ
  | _ :: τs, S n => gen_tsub τs n
  | [], O => O
  | [], S n => n
  end.
