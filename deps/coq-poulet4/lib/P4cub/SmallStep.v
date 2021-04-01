Require Export P4cub.Check.
Require Export P4cub.P4Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Arith.Compare_dec.

Reserved Notation "'ℵ' env '**' e1 '-->' e2"
         (at level 40, e1 custom p4expr, e2 custom p4expr).

(** * Small-Step Values *)
Module IsValue.
  Module P := P4cub.
  Module E := P.Expr.
  Module F := P.F.

  Import P.P4cubNotations.

  Inductive value {tags_t : Type} : E.e tags_t -> Prop :=
  | value_bool (b : bool) (i : tags_t) :
      value <{ BOOL b @ i }>
  | value_bit (w : positive) (n : N) (i : tags_t) :
      value <{ w W n @ i }>
  | value_int (w : positive) (z : Z) (i : tags_t) :
      value <{ w S z @ i }>
  | value_tuple (es : list (E.e tags_t)) (i : tags_t) :
      Forall value es ->
      value <{ tup es @ i }>
  | value_record (fs : F.fs tags_t (E.t tags_t * E.e tags_t))
                 (i : tags_t) :
      F.predfs_data (value ∘ snd) fs ->
      value <{ rec { fs } @ i }>
  | value_header (fs : F.fs tags_t (E.t tags_t * E.e tags_t))
                 (b : E.e tags_t) (i : tags_t) :
      value b ->
      F.predfs_data (value ∘ snd) fs ->
      value <{ hdr { fs } valid:=b @ i }>
  | value_error (err : option (string tags_t)) (i : tags_t) :
      value <{ Error err @ i }>
  | value_matchkind (mk : E.matchkind) (i : tags_t) :
      value <{ Matchkind mk @ i }>
  | value_headerstack (fs : F.fs tags_t (E.t tags_t))
                      (hs : list (E.e tags_t)) (n : positive)
                      (ni : N) :
      Forall value hs ->
      value <{ Stack hs:fs[n] nextIndex:=ni }>.

  Section IsValueInduction.
    Variable tags_t : Type.

    Variable P : E.e tags_t -> Prop.

    Hypothesis HBool : forall b i, P <{ BOOL b @ i }>.

    Hypothesis HBit : forall w n i, P <{ w W n @ i }>.

    Hypothesis HInt : forall w z i, P <{ w S z @ i }>.

    Hypothesis HTuple : forall es i,
      Forall value es ->
      Forall P es ->
      P <{ tup es @ i }>.

    Hypothesis HRecord : forall fs i,
        F.predfs_data (value ∘ snd) fs ->
        F.predfs_data (P ∘ snd) fs ->
        P <{ rec { fs } @ i }>.

    Hypothesis HHeader : forall fs b i,
        value b ->
        P b ->
        F.predfs_data (value ∘ snd) fs ->
        F.predfs_data (P ∘ snd) fs ->
        P <{ hdr { fs } valid:=b @ i }>.

    Hypothesis HError : forall err i, P <{ Error err @ i }>.

    Hypothesis HMatchkind : forall mk i, P <{ Matchkind mk @ i }>.

    Hypothesis HStack : forall fs hs n ni,
        Forall value hs ->
        Forall P hs ->
        P <{ Stack hs:fs[n] nextIndex:=ni }>.

    Definition custom_value_ind : forall (e : E.e tags_t),
        value e -> P e :=
      fix vind (e : E.e tags_t) (H : value e) : P e :=
        let fix lind {es : list (E.e tags_t)}
                (Hes : Forall value es) : Forall P es :=
            match Hes with
            | Forall_nil _ => Forall_nil _
            | Forall_cons _ Hh Ht => Forall_cons _ (vind _ Hh) (lind Ht)
            end in
        let fix find {A : Type} {fs : F.fs tags_t (A * E.e tags_t)}
                (Hfs : F.predfs_data (value ∘ snd) fs) :
              F.predfs_data (P ∘ snd) fs :=
            match Hfs with
            | Forall_nil _ => Forall_nil _
            | Forall_cons _ Hh Ht => Forall_cons _ (vind _ Hh) (find Ht)
            end in
        match H with
        | value_bool b i => HBool b i
        | value_bit w n i => HBit w n i
        | value_int w z i => HInt w z i
        | value_tuple _ i Hes => HTuple _ i Hes (lind Hes)
        | value_record _ i Hfs => HRecord _ i Hfs (find Hfs)
        | value_header _ _ i Hb Hfs => HHeader _ _ i
                                              Hb (vind _ Hb)
                                              Hfs (find Hfs)
        | value_error err i => HError err i
        | value_matchkind mk i => HMatchkind mk i
        | value_headerstack fs _ n ni Hhs => HStack
                                              fs _ n ni
                                              Hhs (lind Hhs)
        end.
  End IsValueInduction.
End IsValue.

Module Step.
  Module P := P4cub.
  Module E := P.Expr.
  Module F := P.F.

  Import P.P4cubNotations.
  Import Env.EnvNotations.

  Module V := IsValue.

  Section StepDefs.
    Context {tags_t : Type}.

    (** Expression environment. *)
    Definition eenv : Type := Env.t (name tags_t) (E.e tags_t).
  End StepDefs.

  Inductive expr_step {tags_t : Type} (ϵ : @eenv tags_t)
    : E.e tags_t -> E.e tags_t -> Prop :=
  | step_var (x : name tags_t) (τ : E.t tags_t)
             (i : tags_t) (e : E.e tags_t) :
      ϵ x = Some e ->
      ℵ ϵ ** Var x:τ @ i -->  e
  | step_cast (τ : E.t tags_t) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** Cast e:τ @ i -->  Cast e':τ @ i
  | step_uop (op : E.uop) (τ : E.t tags_t)
             (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** UOP op e:τ @ i -->  UOP op e':τ @ i
  | step_bop_l (op : E.bop) (τl τr : E.t tags_t)
               (el el' er : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** el -->  el' ->
      ℵ ϵ ** BOP el:τl op er:τr @ i -->  BOP el':τl op er:τr @ i
  | step_bop_r (op : E.bop) (τl τr : E.t tags_t)
               (el er er' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** er -->  er' ->
      ℵ ϵ ** BOP el:τl op er:τr @ i -->  BOP el:τl op er':τr @ i
  | step_member (x : string tags_t) (τ : E.t tags_t)
                (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** Mem e:τ dot x @ i -->  Mem e:τ dot x @ i
  | step_header_op (op : E.hdr_op) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** HDR_OP op e @ i -->  HDR_OP op e' @ i
  | step_stack_op (op : E.hdr_stk_op) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** STK_OP op e @ i -->  STK_OP op e' @ i
  | step_stack_access (e e' : E.e tags_t) (n : N) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** Access e[n] @ i -->  Access e'[n] @ i
  where "'ℵ' ϵ '**' e1 '-->' e2" := (expr_step ϵ e1 e2).
End Step.
