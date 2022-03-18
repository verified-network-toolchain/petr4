From Coq Require Import PArith.BinPos ZArith.BinInt NArith.BinNat.
From Poulet4 Require Export P4cub.Semantics.Climate
     Utils.P4Arith P4cub.Syntax.Syntax.
Import String AllCubNotations.

(** Statement signals. *)
Variant signal : Set :=
| SIG_Cont   (* continue *)
| SIG_Return (* return *).

(** Least-upper bound on signals *)
Definition lub (sg1 sg2 : signal) : signal :=
  match sg1, sg2 with
  | SIG_Cont, _
  | _, SIG_Cont => SIG_Cont
  | _, _        => SIG_Return
  end.

(** Evidence for a type being a numeric of a given width. *)
Variant numeric_width : N -> Expr.t -> Prop :=
| numeric_width_bit : forall w, numeric_width w (Expr.TBit w)
| numeric_width_int : forall w, numeric_width (Npos w) (Expr.TInt w).

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
    (w1 + w2)%positive = w ->
    numeric_width (Npos w2) τ2 ->
    bop_type `++%bop (Expr.TInt w1) τ2 (Expr.TInt w)
| BTPlusPlusIntZero w1 τ2 :
    numeric_width N0 τ2 ->
    bop_type `++%bop (Expr.TInt w1) τ2 (Expr.TInt w1).

(** Evidence a cast is proper. *)
Variant proper_cast : Expr.t -> Expr.t -> Prop :=
| pc_bool_bit : proper_cast Expr.TBool (Expr.TBit 1)
| pc_bit_bool : proper_cast (Expr.TBit 1) Expr.TBool
| pc_bit_int (w : positive) : proper_cast (Expr.TBit (Npos w)) (Expr.TInt w)
| pc_int_bit (w : positive) : proper_cast (Expr.TInt w) (Expr.TBit (Npos w))
| pc_bit_bit (w1 w2 : N) : proper_cast (Expr.TBit w1) (Expr.TBit w2)
| pc_int_int (w1 w2 : positive) : proper_cast (Expr.TInt w1) (Expr.TInt w2)
| pc_tuple_hdr (ts : list Expr.t) :
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

(** Available functions. *)
Definition fenv : Type := Clmt.t string Expr.arrowT.

(** Available actions. *)
Definition aenv : Type := Clmt.t string Expr.params.

(** Control Instance environment. *)
Definition cienv : Type := Clmt.t string (F.fs string string * Expr.params).

(** Parser Instance environment. *)
Definition pienv : Type := Clmt.t string (F.fs string string * Expr.params).

(** Available extern instances. *)
Definition eienv : Type := Clmt.t string (F.fs string Expr.arrowT).

(** Available table names. *)
Definition tblenv : Type := list string.

(** Statement context. *)
Variant ctx : Type :=
| CAction (available_actions : aenv)
          (available_externs : eienv) (* action block *)
| CVoid (* void function *)
| CFunction (return_type : Expr.t) (* fruitful function *)
| CApplyBlock (tables : tblenv)
              (available_actions : aenv)
              (available_controls : cienv)
              (available_externs : eienv) (* control apply block *)
| CParserState (available_parsers : pienv)
               (available_externs : eienv) (* parser state *).
(**[]*)

(** Evidence an extern method call context is ok. *)
Variant extern_call_ok (eis : eienv) : ctx -> Prop :=
| extern_action_ok {aa : aenv} :
    extern_call_ok eis (CAction aa eis)
| extern_apply_block_ok {tbls : tblenv} {aa : aenv} {cis : cienv} :
    extern_call_ok eis (CApplyBlock tbls aa cis eis)
| extern_parser_state_ok {pis : pienv} :
    extern_call_ok eis (CParserState pis eis).
(**[]*)

(** Evidence an action call context is ok. *)
Variant action_call_ok
          (aa : aenv) : ctx -> Prop :=
| action_action_ok {eis : eienv} :
    action_call_ok aa (CAction aa eis)
| action_apply_block_ok {tbls : tblenv} {cis : cienv} {eis : eienv} :
    action_call_ok aa (CApplyBlock tbls aa cis eis).
(**[]*)

(** Evidence an exit context ok. *)
Variant exit_ctx_ok : ctx -> Prop :=
| exit_action_ok {aa : aenv} {eis : eienv} :
    exit_ctx_ok (CAction aa eis)
| exit_applyblk_ok {tbls : tblenv} {aa : aenv}
                   {cis : cienv} {eis : eienv} :
    exit_ctx_ok (CApplyBlock tbls aa cis eis).
(**[]*)

(** Evidence a void return is ok. *)
Variant return_void_ok : ctx -> Prop :=
| return_void_action {aa : aenv} {eis : eienv} :
    return_void_ok (CAction aa eis)
| return_void_void :
    return_void_ok CVoid
| return_void_applyblk {tbls : tblenv} {aa : aenv}
                       {cis : cienv} {eis : eienv} :
    return_void_ok (CApplyBlock tbls aa cis eis).
(**[]*)

(** Available constructor signatures. *)
Definition cenv : Type := Clmt.t string Expr.ct.

(** Available Package Instances. *)
Definition pkgienv : Type := Clmt.t string Expr.ct.

(** Available Extern Constructors. *)
Definition extenv : Type :=
  Clmt.t string (Expr.constructor_params * F.fs string Expr.arrowT).
(**[]*)

Local Open Scope climate_scope.

(** Put parameters into environment. *)

Definition bind_all : Expr.params -> Gamma -> Gamma :=
  F.fold
    (fun x
       '(PADirLess τ
        | PAIn τ
        | PAOut τ
        | PAInOut τ) Γ => x ↦ τ ,, Γ).
(**[]*)

(** Put (constructor) parameters into environments. *)
Definition cbind_all :
  Expr.constructor_params  ->
  Gamma * pkgienv * cienv * pienv * eienv ->
  Gamma * pkgienv * cienv * pienv * eienv :=
  F.fold (fun x c '((Γ, pkgis, cis, pis, eis) as p) =>
            match c with
            | {(VType τ)}
              => ( x ↦ τ,, Γ , pkgis, cis, pis, eis)
            | {(ControlType _ res pars)}
              => (Γ, pkgis,  x ↦ (res,pars),, cis , pis, eis)
            | {(ParserType _ res pars)}
              => (Γ, pkgis, cis,  x ↦ (res,pars),, pis , eis)
            | Expr.CTExtern _
              => p (* TODO! (Γ, pkgis, cis, pis,  x ↦ mhds,, eis ) *)
            | {(PackageType _)}
              => p (* TODO! (Γ,  x ↦ tt,, pkgis , cis, pis, eis) *)
            end).
(**[]*)

(** Environment of user-defined parser states. *)
Definition user_states : Type := list string.

(** Valid parser states. *)
Variant valid_state (us : user_states) : Parser.state -> Prop :=
| start_valid :
    valid_state us ={ start }=
| accept_valid :
    valid_state us ={ accept }=
| reject_valid :
    valid_state us ={ reject }=
| name_valid (st : string) :
    In st us ->
    valid_state us ={ δ st }=.
(**[]*)

(** Appropriate signal. *)
Variant good_signal : Expr.arrowT -> signal -> Prop :=
| good_signal_cont params :
    good_signal {|paramargs:=params; rtrns:=None|} SIG_Cont
| good_signal_return params ret :
    good_signal {|paramargs:=params; rtrns:=Some ret|} SIG_Return.
(**[]*)

Notation "x" := x (in custom p4context at level 0, x constr at level 0).
Notation "'Action' aa eis"
  := (CAction aa eis)
       (in custom p4context at level 0).
Notation "'Void'" := CVoid (in custom p4context at level 0).
Notation "'Function' t"
  := (CFunction t)
       (in custom p4context at level 0, t custom p4type).
Notation "'ApplyBlock' tbls aa cis eis"
  := (CApplyBlock tbls aa cis eis)
       (in custom p4context at level 0).
Notation "'Parser' pis eis"
  := (CParserState pis eis)
       (in custom p4context at level 0).

(** (Syntactic) Evidence an expression may be an lvalue. *)
Inductive lvalue_ok {tags_t : Type} : Expr.e tags_t -> Prop :=
| lvalue_var x τ i :
    lvalue_ok <{ Var x:τ @ i }>
| lvalue_bit_slice e h l i :
    lvalue_ok e ->
    lvalue_ok <{ Slice e [h:l] @ i }>
| lvalue_member t e x i :
    lvalue_ok e ->
    lvalue_ok <{ Mem e dot x : t @ i }>
| lvalue_access ts e idx i :
    lvalue_ok e ->
    lvalue_ok <{ Access e[idx] : ts @ i }>.
(**[]*)
