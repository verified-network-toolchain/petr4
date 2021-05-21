Require Export Poulet4.P4cub.Static.Check.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.micromega.Lia.

(** Notation entries. *)
Declare Custom Entry p4kstmt.

(** * Small-Step Values *)
Module IsValue.
  Module P := P4cub.
  Module E := P.Expr.
  Module F := P.F.

  Import P.P4cubNotations.

  Inductive value {tags_t : Type} : E.e tags_t -> Prop :=
  | value_bool (b : bool) (i : tags_t) :
      value <{ BOOL b @ i }>
  | value_bit (w : positive) (n : Z) (i : tags_t) :
      value <{ w W n @ i }>
  | value_int (w : positive) (z : Z) (i : tags_t) :
      value <{ w S z @ i }>
  | value_tuple (es : list (E.e tags_t)) (i : tags_t) :
      Forall value es ->
      value <{ tup es @ i }>
  | value_record (fs : F.fs string (E.t * E.e tags_t))
                 (i : tags_t) :
      F.predfs_data (value ∘ snd) fs ->
      value <{ rec { fs } @ i }>
  | value_header (fs : F.fs string (E.t * E.e tags_t))
                 (b : E.e tags_t) (i : tags_t) :
      value b ->
      F.predfs_data (value ∘ snd) fs ->
      value <{ hdr { fs } valid:=b @ i }>
  | value_error (err : option (string)) (i : tags_t) :
      value <{ Error err @ i }>
  | value_matchkind (mk : E.matchkind) (i : tags_t) :
      value <{ Matchkind mk @ i }>
  | value_headerstack (fs : F.fs string (E.t))
                      (hs : list (E.e tags_t)) (n : positive)
                      (ni : Z) (i : tags_t) :
      Forall value hs ->
      value <{ Stack hs:fs[n] nextIndex:=ni @ i }>.
  (**[]*)

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

    Hypothesis HStack : forall fs hs n ni i,
        Forall value hs ->
        Forall P hs ->
        P <{ Stack hs:fs[n] nextIndex:=ni @ i }>.

    Definition custom_value_ind : forall (e : E.e tags_t),
        value e -> P e :=
      fix vind (e : E.e tags_t) (H : value e) : P e :=
        let fix lind {es : list (E.e tags_t)}
                (Hes : Forall value es) : Forall P es :=
            match Hes with
            | Forall_nil _ => Forall_nil _
            | Forall_cons _ Hh Ht => Forall_cons _ (vind _ Hh) (lind Ht)
            end in
        let fix find {A : Type} {fs : F.fs string (A * E.e tags_t)}
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
        | value_header _ _ i Hb Hfs
          => HHeader _ _ i Hb (vind _ Hb) Hfs (find Hfs)
        | value_error err i => HError err i
        | value_matchkind mk i => HMatchkind mk i
        | value_headerstack fs _ n ni i Hhs => HStack fs _ n ni i Hhs (lind Hhs)
        end.
  End IsValueInduction.

  Section Lemmas.
    Import F.FieldTactics.

    Hint Constructors value : core.
    Hint Extern 0 => inv_Forall_cons : core.

    Lemma value_exm : forall {tags_t : Type} (e : E.e tags_t), value e \/ ~ value e.
    Proof.
      induction e using E.custom_e_ind; auto 2;
      try (right; intros H'; inv H'; contradiction).
      - assert (Forall value es \/ ~ Forall value es).
        { ind_list_Forall; intuition. }
        intuition. right; intros H'; inv H'. contradiction.
      - assert (F.predfs_data (value ∘ snd) fields \/
                ~ F.predfs_data (value ∘ snd) fields).
        { ind_list_predfs; unfold F.predfs_data in *; intuition. }
        intuition. right; intros H'; inv H'. contradiction.
      - assert (F.predfs_data (value ∘ snd) fields \/
                ~ F.predfs_data (value ∘ snd) fields).
        { ind_list_predfs; unfold F.predfs_data in *; intuition. }
        intuition; right; intros H'; inv H'; contradiction.
      - assert (Forall value hs \/ ~ Forall value hs).
        { ind_list_Forall; intuition. }
        intuition. right; intros H'; inv H'. contradiction.
    Qed.
  End Lemmas.

  Inductive lvalue {tags_t : Type} : E.e tags_t -> Prop :=
  | lvalue_var x τ i :
      lvalue <{ Var x:τ @ i }>
  | lvalue_member lv τ x i :
      lvalue lv ->
      lvalue <{ Mem lv:τ dot x @ i }>
  | lvalue_access lv idx i :
      lvalue lv ->
      lvalue <{ Access lv[idx] @ i }>.
  (**[]*)

  Module CanonicalForms.
    Ltac invert_value :=
      match goal with
      | H: value _ |- _ => inv H
      end.
    (**[]*)

    Import Typecheck.

    Ltac invert_expr_check :=
      match goal with
      | H: ⟦ _, _ ⟧ ⊢ _ ∈ _ |- _ => inv H
      end.
    (**[]*)

    Ltac invert_canonical := invert_value; invert_expr_check.

    Ltac crush_canonical := intros; invert_canonical; eauto 4.

    Section CanonicalForms.
      Variable errs : errors.

      Variable Γ : gamma.

      Context {tags_t : Type}.

      Variable v : E.e tags_t.

      Hypothesis Hv : value v.

      Lemma canonical_forms_bool :
        ⟦ errs, Γ ⟧ ⊢ v ∈ Bool -> exists b i, v = <{ BOOL b @ i }>.
      Proof. crush_canonical. Qed.

      Lemma canonical_forms_bit : forall w,
          ⟦ errs, Γ ⟧ ⊢ v ∈ bit<w> -> exists n i, v = <{ w W n @ i }>.
      Proof. crush_canonical. Qed.

      Lemma canonical_forms_int : forall w,
          ⟦ errs, Γ ⟧ ⊢ v ∈ int<w> -> exists z i, v = <{ w S z @ i }>.
      Proof. crush_canonical. Qed.

      Lemma canonical_forms_tuple : forall ts,
          ⟦ errs, Γ ⟧ ⊢ v ∈ tuple ts -> exists es i, v = <{ tup es @ i }>.
      Proof. crush_canonical. Qed.

      Lemma canonical_forms_record : forall ts,
          ⟦ errs, Γ ⟧ ⊢ v ∈ rec { ts } -> exists fs i, v = <{ rec { fs } @ i }>.
      Proof. crush_canonical. Qed.

      Lemma canonical_forms_header : forall ts,
          ⟦ errs, Γ ⟧ ⊢ v ∈ hdr { ts } -> exists fs b i, v = <{ hdr { fs } valid:=b @ i }>.
      Proof. crush_canonical. Qed.

      Lemma canonical_forms_error :
        ⟦ errs, Γ ⟧ ⊢ v ∈ error -> exists err i, v = <{ Error err @ i }>.
      Proof. crush_canonical. Qed.

      Lemma canonical_forms_matchkind :
        ⟦ errs, Γ ⟧ ⊢ v ∈ matchkind -> exists mk i, v = <{ Matchkind mk @ i }>.
      Proof. crush_canonical. Qed.

      Lemma canonical_forms_headerstack : forall ts n,
          ⟦ errs, Γ ⟧ ⊢ v ∈ stack ts[n] ->
          exists hs ni i, v = <{ Stack hs:ts[n] nextIndex:= ni @ i }>.
      Proof. crush_canonical. Qed.
    End CanonicalForms.

    Ltac inv_eq_val_expr :=
      match goal with
      | H: <{ BOOL _ @ _ }> = <{ BOOL _ @ _ }> |- _ => inv H
      | H: <{ _ W _ @ _ }> = <{ _ W _ @ _ }> |- _ => inv H
      | H: <{ _ S _ @ _ }> = <{ _ S _ @ _ }> |- _ => inv H
      | H: <{ tup _ @ _ }> = <{ tup _ @ _ }> |- _ => inv H
      | H: <{ rec { _ } @ _ }> = <{ rec { _ } @ _ }> |- _ => inv H
      | H: <{ hdr { _ } valid:=_ @ _ }> = <{ hdr { _ } valid:=_ @ _ }>
        |- _ => inv H
      | H: <{ Stack _:_[_] nextIndex:=_ @ _ }> = <{ Stack _:_[_] nextIndex:=_ @ _ }>
        |- _ => inv H
      end.
    (**[]*)

    Ltac assert_canonical_forms :=
      match goal with
      | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ Bool |- _
        => pose proof canonical_forms_bool _ _ _ Hv Ht as [? [? Hcanon]];
          inv Hcanon; inv Hv; inv Ht
      | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ bit<_> |- _
        => pose proof canonical_forms_bit _ _ _ Hv _ Ht as [? [? Hcanon]];
          inv Hcanon; inv Hv; inv Ht
      | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ int<_> |- _
        => pose proof canonical_forms_int _ _ _ Hv _ Ht as [? [? Hcanon]];
          inv Hcanon; inv Hv; inv Ht
      | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ tuple _ |- _
        => pose proof canonical_forms_tuple _ _ _ Hv _ Ht as [? [? Hcanon]];
          inv Hcanon; inv Hv; inv Ht
      | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ rec { _ } |- _
        => pose proof canonical_forms_record _ _ _ Hv _ Ht as [? [? Hcanon]];
          inv Hcanon; inv Hv; inv Ht
      | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ hdr { _ } |- _
        => pose proof canonical_forms_header _ _ _ Hv _ Ht as [? [? [? Hcanon]]];
          inv Hcanon; inv Hv; inv Ht
      | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ error |- _
        => pose proof canonical_forms_error _ _ _ Hv Ht as [? [? Hcanon]];
          inv Hcanon; inv Hv; inv Ht
      | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ matchkind |- _
        => pose proof canonical_forms_matchkind _ _ _ Hv Ht as [? [? Hcanon]];
          inv Hcanon; inv Hv; inv Ht
      | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ stack _[_] |- _
        => pose proof canonical_forms_headerstack _ _ _ Hv _ _ Ht as [? [? [? Hcanon]]];
          inv Hcanon; inv Hv; inv Ht
      end.
    (**[]*)
  End CanonicalForms.
End IsValue.

Module Step.
  Module P := P4cub.
  Module E := P.Expr.
  Module ST := P.Stmt.
  Module F := P.F.
  Module PT := E.ProperType.
  Module PR := P.Parser.
  Import P.P4cubNotations.
  Import Env.EnvNotations.
  Module V := IsValue.

  Section StepDefs.
    Import Typecheck.
    Import E.TypeEquivalence.
    Import E.ProperType.
    Import F.FieldTactics.
    Import P4ArithTactics.

    Context {tags_t : Type}.

    (** Expression environment. *)
    Definition eenv : Type := Env.t (string) (E.e tags_t).

    (** Bit-slicing. *)
    Definition eval_slice (hi lo : positive) (v : E.e tags_t) : option (E.e tags_t) :=
      match v with
      | <{ _ W z @ i }>
      | <{ _ S z @ i }>
        => let w' := (hi - lo + 1)%positive in
        Some $ E.EBit w'
             (BitArith.mod_bound w' $
              BitArith.bitstring_slice z hi lo) i
      | _ => None
      end.
    (**[]*)

    Definition eval_cast
               (target : E.t) (v : E.e tags_t) : option (E.e tags_t) :=
      match target, v with
      | {{ bit<xH> }}, <{ TRUE @ i }>         => Some (E.EBit 1%positive 1%N i)
      | {{ bit<xH> }}, <{ FALSE @ i }>        => Some (E.EBit 1%positive 0%N i)
      | {{ Bool }}, E.EBit 1%positive 1%N i => Some <{ TRUE @ i }>
      | {{ Bool }}, E.EBit 1%positive 0%N i => Some <{ FALSE @ i }>
      | {{ bit<w> }}, E.EInt _ z i
        => let n := BitArith.mod_bound w z in
          Some <{ w W n @ i }>
      | {{ int<w> }}, <{ _ W n @ i }>
        => let z := IntArith.mod_bound w n in
          Some <{ w S z @ i }>
      | {{ bit<w> }}, <{ _ W n @ i }>
        => let n := BitArith.mod_bound w n in
          Some <{ w W n @ i }>
      | {{ int<w> }}, <{ _ S z @ i}>
        => let z := IntArith.mod_bound w z in
          Some <{ w S z @ i }>
      | {{ rec { fs } }}, <{ tup vs @ i }>
        => Some $ E.ERecord (combine (F.keys fs) $ combine (F.values fs) vs) i
      | {{ hdr { fs } }}, <{ tup vs @ i }>
        => Some
            $ E.EHeader
            (combine (F.keys fs) $ combine (F.values fs) vs) <{ TRUE @ i }> i
      | _, _ => None
      end.
    (**[]*)

    (** Default (value) Expression. *)
    Fixpoint edefault (i : tags_t) (τ : E.t) : E.e tags_t :=
      let fix lrec (ts : list (E.t)) : list (E.e tags_t) :=
          match ts with
          | []     => []
          | τ :: ts => edefault i τ :: lrec ts
          end in
      let fix frec (fs : F.fs string (E.t))
          : F.fs string (E.t * E.e tags_t) :=
          match fs with
          | [] => []
          | (x, τ) :: fs => (x, (τ, edefault i τ)) :: frec fs
          end in
      match τ with
      | {{ Bool }} => <{ BOOL false @ i }>
      | {{ bit<w> }} => E.EBit w 0%Z i
      | {{ int<w> }} => E.EInt w 0%Z i
      | {{ error }} => <{ Error None @ i }>
      | {{ matchkind }} => <{ Matchkind exact @ i }>
      | {{ tuple ts }} => E.ETuple (lrec ts) i
      | {{ rec { fs } }} => E.ERecord (frec fs) i
      | {{ hdr { fs } }} => E.EHeader (frec fs) <{ BOOL false @ i }> i
      | {{ stack tfs[n] }}
          => let tefs := frec tfs in
            let hs :=
                repeat
                <{ hdr { tefs } valid:= BOOL false @ i @ i }>
                (Pos.to_nat n) in
            E.EHeaderStack tfs hs n 0%Z i
      end.
    (**[]*)

    (** Unary Operations. *)
    Definition eval_uop (op : E.uop) (e : E.e tags_t) : option (E.e tags_t) :=
      match op, e with
      | _{ ! }_, <{ BOOL b @ i }>
        => let b' := negb b in Some <{ BOOL b' @ i }>
      | _{ ~ }_, <{ w W n @ i }>
        => let n' := BitArith.bit_not w n in Some <{ w W n' @ i }>
      | _{ ~ }_, <{ w S n @ i }>
        => let n' := IntArith.bit_not w n in Some <{ w S n' @ i }>
      | _{ - }_, <{ w W z @ i }>
        => let z' := BitArith.neg w z in Some <{ w W z' @ i }>
      | _{ - }_, <{ w S z @ i }>
        => let z' := IntArith.neg w z in Some <{ w S z' @ i }>
      | _{ isValid }_, <{ hdr { _ } valid:=b @ i }> => Some b
      | _{ setValid }_, <{ hdr { fs } valid:=_ @ i }>
        => Some <{ hdr { fs } valid:=TRUE @ i @ i}>
      | _{ setInValid }_, <{ hdr { fs } valid:=b @ i }>
        => Some <{ hdr { fs } valid:=FALSE @ i @ i }>
      | _{ Size }_, <{ Stack _:_[size] nextIndex:=_ @ i }>
        => let w := 32%positive in
          let s := Zpos size in Some <{ w W s @ i }>
      | _{ Next }_, <{ Stack hs:_[_] nextIndex:=ni @ _ }>
        => nth_error hs $ Z.to_nat ni
      | _{ Push p }_, <{ Stack hs:ts[n] nextIndex:=ni @ i }>
        => let pnat := Pos.to_nat p in
          let sizenat := Pos.to_nat n in
          let hdefault :=
              E.EHeader
                (F.map (fun τ => (τ, edefault i τ)) ts)
              <{ BOOL false @ i }> i in
          if lt_dec pnat sizenat then
            let new_hdrs := repeat hdefault pnat in
            let remains := firstn (sizenat - pnat) hs in
            Some $ E.EHeaderStack ts (new_hdrs ++ remains) n
                 (Z.min (ni + Zpos p)%Z (Z.pos n - 1)%Z) i
          else
            let new_hdrs := repeat hdefault sizenat in
            Some $ E.EHeaderStack ts new_hdrs n (Z.pos n - 1)%Z i
      | _{ Pop p }_, <{ Stack hs:ts[n] nextIndex:=ni @ i }>
        => let pnat := Pos.to_nat p in
          let sizenat := Pos.to_nat n in
          let hdefault :=
              E.EHeader
                (F.map (fun τ => (τ, edefault i τ)) ts)
              <{ BOOL false @ i }> i in
          if lt_dec pnat sizenat then
            let new_hdrs := repeat hdefault pnat in
            let remains := skipn pnat hs in
            Some $ E.EHeaderStack ts (remains ++ new_hdrs) n
                 (Z.max 0 (ni - Zpos p)%Z) i
          else
            let new_hdrs := repeat hdefault sizenat in
            Some $ E.EHeaderStack ts new_hdrs n 0%N i
      | _, _ => None
      end.
    (**[]*)

    (** Binary operations. *)
    Definition eval_bop
               (op : E.bop) (v1 v2 : E.e tags_t) (i : tags_t) : option (E.e tags_t) :=
      match op, v1, v2 with
      | +{ + }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some $ E.EBit w (BitArith.plus_mod w n1 n2) i
      | +{ + }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some $ E.EInt w (IntArith.plus_mod w z1 z2) i
      | +{ |+| }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some $ E.EBit w (BitArith.plus_sat w n1 n2) i
      | +{ |+| }+,  <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some $ E.EInt w (IntArith.plus_sat w z1 z2) i
      | +{ - }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some $ E.EBit w (BitArith.minus_mod w n1 n2) i
      | +{ - }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some $ E.EInt w (IntArith.minus_mod w z1 z2) i
      | +{ |-| }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some $ E.EBit w (BitArith.minus_sat w n1 n2) i
      | +{ |-| }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some $ E.EInt w (IntArith.minus_sat w z1 z2) i
      | +{ × }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some $ E.EBit w (BitArith.mult_mod w n1 n2) i
      | +{ × }+, <{ w S n1 @ _ }>, <{ _ S n2 @ _ }>
        => Some $ E.EInt w (IntArith.mult_mod w n1 n2) i
      | +{ << }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some $ E.EBit w (BitArith.shift_left w n1 n2) i
      | +{ << }+, <{ w S z1 @ _ }>, <{ _ W z2 @ _ }>
        => Some $ E.EInt w (IntArith.shift_left w z1 z2) i
      | +{ >> }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some $ E.EBit w (BitArith.shift_right w n1 n2) i
      | +{ >> }+, <{ w S z1 @ _ }>, <{ _ W z2 @ _ }>
        => Some $ E.EInt w (IntArith.shift_right w z1 z2) i
      | +{ & }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some $ E.EBit w (BitArith.bit_and w n1 n2) i
      | +{ & }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some $ E.EInt w (IntArith.bit_and w z1 z2) i
      | +{ ^ }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some $ E.EBit w (BitArith.bit_xor w n1 n2) i
      | +{ ^ }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some $ E.EInt w (IntArith.bit_xor w z1 z2) i
      | +{ | }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some $ E.EBit w (BitArith.bit_or w n1 n2) i
      | +{ | }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some $ E.EInt w (IntArith.bit_or w z1 z2) i
      | +{ <= }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ E.EBool (n1 <=? n2)%Z i
      | +{ <= }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ E.EBool (z1 <=? z2)%Z i
      | +{ < }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ E.EBool (n1 <? n2)%Z i
      | +{ < }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ E.EBool (z1 <? z2)%Z i
      | +{ >= }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ E.EBool (n2 <=? n1)%Z i
      | +{ >= }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ E.EBool (z2 <=? z1)%Z i
      | +{ > }+, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some $ E.EBool (n2 <? n1)%Z i
      | +{ > }+, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some $ E.EBool (z2 <? z1)%Z i
      | +{ && }+, <{ BOOL b1 @ _ }>, <{ BOOL b2 @ _ }> => Some $ E.EBool (b1 && b2) i
      | +{ || }+, <{ BOOL b1 @ _ }>, <{ BOOL b2 @ _ }> => Some $ E.EBool (b1 || b2) i
      | +{ == }+, _, _ => Some $ E.EBool (E.ExprEquivalence.eqbe v1 v2) i
      | +{ != }+, _, _ => Some $ E.EBool (negb $ E.ExprEquivalence.eqbe v1 v2) i
      | +{ ++ }+, <{ w1 W n1 @ _ }>, <{ w2 W n2 @ _ }>
      | +{ ++ }+, <{ w1 W n1 @ _ }>, <{ w2 S n2 @ _ }>
        => Some $ E.EBit (w1 + w2)%positive (BitArith.concat w1 w2 n1 n2) i
      | +{ ++ }+, <{ w1 S n1 @ _ }>, <{ w2 S n2 @ _ }>
      | +{ ++ }+, <{ w1 S n1 @ _ }>, <{ w2 W n2 @ _ }>
        => Some $ E.EInt (w1 + w2)%positive (IntArith.concat w1 w2 n1 n2) i
      | _, _, _ => None
      end.
    (**[]*)

    (** Get header stack data from value. *)
    Definition header_stack_data (v : E.e tags_t)
      : option (positive * Z *
                F.fs string (E.t) *
                (list (E.e tags_t))) :=
      match v with
      | <{ Stack hs:ts[n] nextIndex:=ni @ _}> => Some (n,ni,ts,hs)
      | _ => None
      end.
    (**[]*)

    Definition eval_member (x : string) (v : E.e tags_t) : option (E.e tags_t) :=
      match v with
      | <{ rec { vs } @ _ }>
      | <{ hdr { vs } valid:=_ @ _ }> => vs ▷ F.get x >>| snd
      | _                             => None
      end.
    (**[]*)

    Section Edefault.
      Local Hint Constructors V.value : core.

      Lemma value_edefault : forall i τ, V.value (edefault i τ).
      Proof.
        induction τ using E.custom_t_ind; unravel; auto 1;
        try (constructor; apply repeat_Forall); constructor; auto 1;
        try (ind_list_predfs; unfold F.predfs_data in * );
        try ind_list_Forall; unravel in *; auto 4.
      Qed.
    End Edefault.

    Section HelpersType.
      Local Hint Constructors check_expr : core.
      Local Hint Extern 0 => bit_bounded : core.
      Local Hint Extern 0 => int_bounded : core.

      Import V.CanonicalForms.

      Lemma eval_slice_types : forall errs Γ v v' τ hi lo w,
          eval_slice hi lo v = Some v' ->
          V.value v ->
          (lo <= hi < w)%positive ->
          numeric_width w τ ->
          ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
          let w' := (hi - lo + 1)%positive in
          ⟦ errs, Γ ⟧ ⊢ v' ∈ bit<w'>.
      Proof.
        intros errs Γ v v' τ hi lo w Heval Hv Hw Hnum Ht w'; subst w';
        inv Hnum; assert_canonical_forms; unravel in *; inv Heval; auto 2.
      Qed.

      Local Hint Resolve BitArith.bound0 : core.
      Local Hint Resolve BitArith.bound1 : core.
      Local Hint Resolve IntArith.bound0 : core.

      Lemma eval_cast_types : forall errs Γ τ τ' v v',
          eval_cast τ' v = Some v' ->
          V.value v ->
          proper_cast τ τ' ->
          ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
          ⟦ errs, Γ ⟧ ⊢ v' ∈ τ'.
      Proof.
        intros errs Γ τ τ' v v' Heval Hv Hpc Ht;
        inv Hpc; assert_canonical_forms; unravel in *;
        try match goal with
            | H: context [ if ?b then _ else _ ]
              |- _ => destruct b eqn:?
            end; try (inv Heval; auto 2; assumption).
        - destruct x; try (inv Heval; auto 2; assumption).
          destruct p; inv Heval; auto 2.
        - destruct w; inv Heval; auto 2.
        - destruct w2; inv Heval; auto 2.
        - inv Heval. constructor.
          generalize dependent fs.
          ind_list_Forall; intros [| [? ?] ?] ?;
          unravel in *; try inv_Forall2_cons;
          constructor; try split;
          unravel; try apply IHx; auto 2.
        - inv Heval; constructor; auto 1.
          + apply pn_header. rewrite F.predfs_data_map. assumption.
          + clear x0 H0. generalize dependent fs.
            ind_list_Forall; intros [| [? ?] ?] ? ;
            unravel in *; try inv_Forall2_cons;
            constructor; try split;
            unravel; try apply IHx; auto 2.
      Qed.

      Lemma eval_bop_types : forall Γ errs op τ1 τ2 τ (i : tags_t) v1 v2 v,
          bop_type op τ1 τ2 τ ->
          V.value v1 -> V.value v2 ->
          eval_bop op v1 v2 i = Some v ->
          ⟦ errs, Γ ⟧ ⊢ v1 ∈ τ1 -> ⟦ errs, Γ ⟧ ⊢ v2 ∈ τ2 -> ⟦ errs, Γ ⟧ ⊢ v ∈ τ.
      Proof.
        intros Γ errs op τ1 τ2 τ v1 v2 v i Hbop Hv1 Hv2 Heval Ht1 Ht2;
        inv Hbop; unravel in *; try inv_numeric;
        repeat assert_canonical_forms;
        try (inv_numeric_width; assert_canonical_forms);
        try (inv Heval; auto 2; assumption).
      Qed.

      Lemma eval_member_types : forall errs Γ x v v' ts τ τ',
          eval_member x v = Some v' ->
          V.value v ->
          member_type ts τ ->
          F.get x ts = Some τ' ->
          ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
          ⟦ errs, Γ ⟧ ⊢ v' ∈ τ'.
      Proof.
        intros errs Γ x v v' ts τ τ' Heval Hv Hmem Hget Ht;
        inv Hmem; assert_canonical_forms.
        - eapply F.relfs_get_r in H1 as [[? ?] [? ?]]; eauto 2;
          unravel in *; rewrite H in Heval;
          unravel in *; inv Heval; intuition.
        - eapply F.relfs_get_r in H6 as [[? ?] [? ?]]; eauto 2;
          unravel in *; rewrite H in Heval;
          unravel in *; inv Heval; intuition.
      Qed.

      Local Hint Constructors proper_nesting : core.
      Hint Rewrite repeat_length.
      Local Hint Resolve proper_inside_header_nesting : core.
      Local Hint Resolve BitArith.bound0 : core.
      Local Hint Resolve IntArith.bound0 : core.
      Local Hint Constructors error_ok : core.

      Lemma edefault_types : forall errs Γ i τ,
          PT.proper_nesting τ ->
          let e := edefault i τ in
          ⟦ errs, Γ ⟧ ⊢ e ∈ τ.
      Proof.
        intros; subst e; induction τ using E.custom_t_ind; unravel;
        invert_proper_nesting; auto 2;
        constructor; autorewrite with core; auto 2;
        try (apply repeat_Forall; constructor; auto 2);
        try (ind_list_Forall; repeat inv_Forall_cons; constructor; intuition);
        try (ind_list_predfs; repeat invert_cons_predfs; constructor;
             try split; unravel; intuition).
      Qed.

      Local Hint Resolve Forall_impl : core.
      Local Hint Resolve Forall_firstn : core.
      Local Hint Resolve Forall_skipn : core.
      Local Hint Resolve proper_inside_header_nesting : core.
      Local Hint Resolve edefault_types : core.
      Hint Rewrite app_length.
      Hint Rewrite Forall_app.
      Hint Rewrite firstn_length_le.
      Hint Rewrite skipn_length.
      Hint Rewrite map_length.
      Hint Rewrite (@F.predfs_data_map string).
      Hint Rewrite @F.map_fst.
      Hint Rewrite @map_compose.
      Hint Rewrite (@Forall2_map_l E.t).
      Hint Rewrite (@Forall2_Forall E.t).
      Hint Rewrite (@F.predfs_data_map).
      Hint Rewrite @F.relfs_split_map_iff.
      Hint Rewrite @F.map_snd.

      Lemma eval_uop_types : forall errs Γ op e v τ τ',
          uop_type op τ τ' -> V.value e -> eval_uop op e = Some v ->
          ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> ⟦ errs, Γ ⟧ ⊢ v ∈ τ'.
      Proof.
        intros errs Γ op e v τ τ' Huop Hev Heval Het;
        inv Huop; try inv_numeric;
        assert_canonical_forms; unravel in *;
        inv Heval; auto 2; invert_proper_nesting;
        repeat match goal with
               | H: (if ?b then _ else _) = Some _
                 |- _ => destruct b as [? | ?] eqn:?
               | H: Some _ = Some _ |- _ => inv H
               end; eauto 2;
        try constructor; auto 2; try (destruct n; lia);
        autorewrite with core; try lia;
        try split; auto 2;
        try (apply repeat_Forall; constructor; auto 2;
             autorewrite with core in *; split; [intuition | unravel; eauto 5]).
        - eapply Forall_nth_error in H9; eauto 1; simpl in *; auto 1.
      Qed.
    End HelpersType.

    Section HelpersExist.
      Import V.CanonicalForms.

      Lemma eval_slice_exists : forall errs Γ v τ hi lo w,
        V.value v ->
        (lo <= hi < w)%positive ->
        numeric_width w τ ->
        ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
        exists v', eval_slice hi lo v = Some v'.
      Proof.
        intros errs Γ v τ hi lo w Hv Hw Hnum Ht;
        inv Hnum; assert_canonical_forms; unravel; eauto 2.
      Qed.

      Lemma eval_cast_exists : forall errs Γ e τ τ',
        V.value e ->
        proper_cast τ τ' ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        exists v, eval_cast τ' e = Some v.
      Proof.
        intros ? ? ? ? ? Hv Hpc Het; inv Hpc; assert_canonical_forms;
          unravel; simpl in *; eauto 2.
        - destruct x; eauto 2.
        - destruct x; eauto 2; destruct p; eauto 2;
          try (cbv in H0; destruct H0; try destruct p; discriminate).
        - destruct w; eauto 2.
        - destruct w2; eauto 2.
      Qed.

      Lemma eval_bop_exists : forall errs Γ op τ1 τ2 τ (i : tags_t) v1 v2,
          bop_type op τ1 τ2 τ ->
          V.value v1 -> V.value v2 ->
          ⟦ errs, Γ ⟧ ⊢ v1 ∈ τ1 -> ⟦ errs, Γ ⟧ ⊢ v2 ∈ τ2 ->
          exists v, eval_bop op v1 v2 i = Some v.
      Proof.
        intros errs Γ op τ1 τ2 τ i v1 v2 Hbop Hv1 Hv2 Ht1 Ht2;
        inv Hbop; try inv_numeric; try inv_numeric_width;
        repeat assert_canonical_forms; unravel; eauto 2.
      Qed.

      Lemma eval_uop_exists : forall op errs Γ e τ τ',
          uop_type op τ τ' -> V.value e -> ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
          exists v, eval_uop op e = Some v.
      Proof.
        intros op errs Γ e τ τ' Hu Hv Het; inv Hu;
        try inv_numeric; assert_canonical_forms;
        unravel; eauto 2.
        - assert (Hnihs : (Z.to_nat x0 < length x)%nat) by lia.
          pose proof nth_error_exists _ _ Hnihs as [? Hnth].
          rewrite Hnth; eauto 2.
        - destruct (lt_dec (Pos.to_nat p) (Pos.to_nat n)) as [? | ?]; eauto 2.
        - destruct (lt_dec (Pos.to_nat p) (Pos.to_nat n)) as [? | ?]; eauto 2.
      Qed.

      Lemma eval_member_exists : forall errs Γ x v ts τ τ',
          V.value v ->
          member_type ts τ ->
          F.get x ts = Some τ' ->
          ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
          exists v', eval_member x v = Some v'.
      Proof.
        intros errs Γ x v ts τ τ' Hv Hmem Hget Ht;
        inv Hmem; assert_canonical_forms; unravel.
        - eapply F.relfs_get_r in H1 as [[? ?] [? ?]]; eauto 2;
          unravel in *; rewrite H; unravel; eauto 2.
        - eapply F.relfs_get_r in H6 as [[? ?] [? ?]]; eauto 2;
          unravel in *; rewrite H; unravel; eauto 2.
      Qed.
    End HelpersExist.

    (** Lookup an lvalue. *)
    Fixpoint lv_lookup (ϵ : eenv) (lv : E.e tags_t) : option (E.e tags_t) :=
      match lv with
      | <{ Var x:_ @ _ }> => ϵ x
      | <{ Mem lv:_ dot x @ _ }> =>
        (* TODO: use monadic bind. *)
        match lv_lookup ϵ lv with
        | Some <{ rec { fs } @ _ }>
        | Some <{ hdr { fs } valid:=_  @ _ }> => fs ▷ F.get x >>| snd
        | _ => None
        end
      | <{ Access lv[n] @ _ }> =>
        match lv_lookup ϵ lv with
        | Some <{ Stack vss:_[_] nextIndex:=_ @ _ }> => nth_error vss (Z.to_nat n)
        | _ => None
        end
      | _ => None
      end.
    (**[]*)

    (** Updating an lvalue in an environment. *)
    Fixpoint lv_update (lv v : E.e tags_t) (ϵ : eenv) : eenv :=
      match lv with
      | <{ Var x:_ @ _ }> => !{ x ↦ v ;; ϵ }!
      | <{ Mem lv:_ dot x @ _ }> =>
        match lv_lookup ϵ lv with
        | Some <{ rec { vs } @ i }>
          => match F.get x vs with
            | None => ϵ
            | Some (τ,_) => lv_update lv (E.ERecord (F.update x (τ,v) vs) i) ϵ
            end
        | Some <{ hdr { vs } valid:=b @ i }>
          => match F.get x vs with
            | None => ϵ
            | Some (τ,_) => lv_update lv (E.EHeader (F.update x (τ,v) vs) b i) ϵ
            end
        | _ => ϵ
        end
      | <{ Access lv[n] @ _ }> =>
        match lv_lookup ϵ lv with
        | Some <{ Stack vss:ts[size] nextIndex:=ni @ i }> =>
          let vss := nth_update (Z.to_nat n) v vss in
          lv_update lv <{ Stack vss:ts[size] nextIndex:=ni @ i }> ϵ
        | _ => ϵ
        end
      | _ => ϵ
      end.
    (**[]*)

    (** Create a new environment
        from a closure environment where
        values of [In] args are substituted
        into the function parameters. *)
    Definition copy_in
               (argsv : E.args tags_t)
               (ϵcall : eenv) : eenv -> eenv :=
      F.fold (fun x arg ϵ =>
                match arg with
                | P.PAIn (_,v)     => !{ x ↦ v ;; ϵ }!
                | P.PAInOut (_,lv) => match lv_lookup ϵcall lv with
                                     | None   => ϵ
                                     | Some v => !{ x ↦ v ;; ϵ }!
                                     end
                | P.PAOut _    => ϵ
                end) argsv.
    (**[]*)

    (** Update call-site environment with
        out variables from function call evaluation. *)
    Definition copy_out
               (argsv : E.args tags_t)
               (ϵf : eenv) : eenv -> eenv :=
      F.fold (fun x arg ϵ =>
                match arg with
                | P.PAIn _ => ϵ
                | P.PAOut (_,lv)
                | P.PAInOut (_,lv) =>
                  match ϵf x with
                  | None   => ϵ
                  | Some v => lv_update lv v ϵ
                  end
                end) argsv.
    (**[]*)

    (** Table environment. *)
    Definition tenv : Type := Env.t string (CD.table tags_t).

    (** Function declarations and closures. *)
    Inductive fdecl : Type :=
    | FDecl (closure : eenv) (fs : fenv) (ins : ienv) (body : ST.s tags_t)
    with fenv : Type :=
    | FEnv (fs : Env.t string fdecl)
    (** Action declarations and closures *)
    with adecl : Type :=
    | ADecl (closure : eenv) (fs : fenv) (ins : ienv) (aa : aenv) (body : ST.s tags_t)
    with aenv : Type :=
    | AEnv (aa : Env.t string adecl)
    (** Instances and Environment. *)
    with inst : Type :=
    | CInst (closure : eenv) (fs : fenv) (ins : ienv)
            (tbls : tenv) (aa : aenv)
            (apply_blk : ST.s tags_t)  (* control instance *)
    | PInst (* TODO: parser instance *)
    | EInst (* TODO: extern object instance *)
    with ienv : Type :=
    | IEnv (ins : Env.t string inst).
    (**[]*)

    (** Function lookup. *)
    Definition lookup '(FEnv fs : fenv) : string -> option fdecl := fs.

    (** Bind a function declaration to an environment. *)
    Definition update '(FEnv fs : fenv) (x : string) (d : fdecl) : fenv :=
      FEnv !{ x ↦ d ;; fs }!.
    (**[]*)

    (** Instance lookup. *)
    Definition ilookup '(IEnv fs : ienv) : string -> option inst := fs.

    (** Bind an instance to an environment. *)
    Definition iupdate '(IEnv fs : ienv) (x : string) (d : inst) : ienv :=
      IEnv !{ x ↦ d ;; fs }!.
    (**[]*)

    (** Action lookup. *)
    Definition alookup '(AEnv aa : aenv) : string -> option adecl := aa.

    (** Bind a function declaration to an environment. *)
    Definition aupdate '(AEnv aa : aenv) (x : string) (d : adecl) : aenv :=
      AEnv !{ x ↦ d ;; aa }!.
    (**[]*)

    (** Control plane table entries,
        essentially mapping tables to an action call. *)
    Definition entries : Type :=
      list (E.e tags_t * E.matchkind) ->
      list string ->
      string * E.args tags_t.
    (**[]*)

    (** Control plane configuration. *)
    Definition ctrl : Type := Env.t string entries.

    (** Control declarations and closures. *)
    Inductive cdecl : Type :=
    | CDecl (cs : cenv) (closure : eenv) (fs : fenv) (ins : ienv)
            (body : CD.d tags_t) (apply_block : ST.s tags_t)
    with cenv : Type :=
    | CEnv (cs : Env.t string cdecl).
    (**[]*)

    (** Control lookup. *)
    Definition clookup '(CEnv cs : cenv) : string -> option cdecl := cs.

    (** Bind an instance to an environment. *)
    Definition cupdate '(CEnv cs : cenv) (x : string) (d : cdecl) : cenv :=
      CEnv !{ x ↦ d ;; cs }!.
    (**[]*)

    (** Continuation statements. *)
    Inductive kstmt : Type :=
    | KStop                              (* end of continuation *)
    | KSeq (s : ST.s tags_t) (k : kstmt) (* sequencing/composition *)
    | KBlock (ϵ : eenv) (k : kstmt)      (* block: enclosing environment & continuation *)
    | KCall (args : E.arrowE tags_t)
            (ϵ : eenv) (k : kstmt)       (* function/procedure
                                            call-site with arguments,
                                            enclosing environment, & continuation *)
    | KExit (k : kstmt)                  (* exit statement control-flow *)
    | KReturn (o : option (E.e tags_t))
              (k : kstmt)                (* return statement control-flow *).
    (**[]*)
  End StepDefs.

  Notation "'k{' s '}k'" := s (s custom p4kstmt at level 99).
  Notation "( x )" := x (in custom p4kstmt, x at level 99).
  Notation "x" := x (in custom p4kstmt at level 0, x constr at level 0).
  Notation "'κ' s '⋅' k"
    := (KSeq s k)
         (in custom p4kstmt at level 99, s custom p4stmt,
             k custom p4kstmt, right associativity).
  Notation "'∫' env '⊗' k"
    := (KBlock env k)
         (in custom p4kstmt at level 99, env custom p4env,
             k custom p4kstmt, right associativity).
  Notation "'Λ' ( args , env ) k"
    := (KCall args env k)
         (in custom p4kstmt at level 99, env custom p4env,
             k custom p4kstmt, right associativity).
  Notation "'EXIT' k"
           := (KExit k)
                (in custom p4kstmt at level 99,
                    k custom p4kstmt, right associativity).
  Notation "'RETURN' o k"
           := (KReturn o k)
                (in custom p4kstmt at level 99,
                    k custom p4kstmt, right associativity).
  Notation "'VOID' k"
           := (KReturn None k)
                (in custom p4kstmt at level 99,
                    k custom p4kstmt, right associativity).
  Notation "'FRUIT' e k"
           := (KReturn (Some e) k)
                (in custom p4kstmt at level 99,
                    k custom p4kstmt, right associativity).

  Reserved Notation "'ℵ' env , e1 '-->' e2"
           (at level 40, e1 custom p4expr, e2 custom p4expr).

  (** Expression evaluation. *)
  Inductive expr_step {tags_t : Type} (ϵ : eenv)
    : E.e tags_t -> E.e tags_t -> Prop :=
  | step_var (x : string) (τ : E.t)
             (i : tags_t) (e : E.e tags_t) :
      ϵ x = Some e ->
      ℵ ϵ, Var x:τ @ i -->  e
  | step_slice (e e' : E.e tags_t) (τ : E.t)
               (hi lo : positive) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
      ℵ ϵ, Slice e:τ [hi:lo] @ i -->  Slice e':τ [hi:lo] @ i
  | step_slice_eval (v v' : E.e tags_t) (τ : E.t)
                    (hi lo : positive) (i : tags_t) :
      eval_slice hi lo v = Some v' ->
      V.value v ->
      ℵ ϵ, Slice v:τ [hi:lo] @ i -->  v'
  | step_cast (τ : E.t) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
      ℵ ϵ, Cast e:τ @ i -->  Cast e':τ @ i
  | step_cast_eval (τ : E.t) (v v' : E.e tags_t) (i : tags_t) :
      eval_cast τ v = Some v' ->
      V.value v ->
      ℵ ϵ, Cast v:τ @ i -->  v'
  | step_uop (op : E.uop) (τ : E.t)
             (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
      ℵ ϵ, UOP op e:τ @ i -->  UOP op e':τ @ i
  | step_uop_eval (op : E.uop) (τ : E.t)
                  (v v' : E.e tags_t) (i : tags_t) :
      eval_uop op v = Some v' ->
      V.value v ->
      ℵ ϵ, UOP op v:τ @ i -->  v'
  | step_bop_l (op : E.bop) (τl τr : E.t)
               (el el' er : E.e tags_t) (i : tags_t) :
      ℵ ϵ, el -->  el' ->
      ℵ ϵ, BOP el:τl op er:τr @ i -->  BOP el':τl op er:τr @ i
  | step_bop_r (op : E.bop) (τl τr : E.t)
               (vl er er' : E.e tags_t) (i : tags_t) :
      V.value vl ->
      ℵ ϵ, er -->  er' ->
      ℵ ϵ, BOP vl:τl op er:τr @ i -->  BOP vl:τl op er':τr @ i
  | step_bop_eval (op : E.bop) (τl τr : E.t)
                  (vv vl vr : E.e tags_t) (i : tags_t) :
      eval_bop op vl vr i = Some vv ->
      V.value vl -> V.value vr ->
      ℵ ϵ, BOP vl:τl op vr:τr @ i -->  vv
  | step_member (x : string) (τ : E.t)
                (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
      ℵ ϵ, Mem e:τ dot x @ i -->  Mem e:τ dot x @ i
  | step_member_eval (x : string) (τ : E.t)
                     (v v' : E.e tags_t) (i : tags_t) :
      eval_member x v = Some v' ->
      V.value v ->
      ℵ ϵ, Mem v:τ dot x @ i -->  v'
  | step_stack_access (e e' : E.e tags_t) (n : Z) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
      ℵ ϵ, Access e[n] @ i -->  Access e'[n] @ i
  | step_stack_access_eval (v v' : E.e tags_t) (n : Z) (i : tags_t) :
      header_stack_data v >>| fourple_4 >>=
                 (fun hs => nth_error hs (Z.to_nat n)) = Some v' ->
      V.value v ->
      ℵ ϵ, Access v[n] @ i -->  v'
  | step_tuple (prefix suffix : list (E.e tags_t))
               (e e' : E.e tags_t) (i : tags_t) :
      Forall V.value prefix ->
      ℵ ϵ, e -->  e' ->
      let es := prefix ++ e :: suffix in
      let es' := prefix ++ e' :: suffix in
      ℵ ϵ, tup es @ i -->  tup es' @ i
  | step_record (prefix suffix : F.fs string (E.t * E.e tags_t))
                (x : string) (τ : E.t)
                (e e' : E.e tags_t) (i : tags_t) :
      F.predfs_data (V.value ∘ snd) prefix ->
      ℵ ϵ, e -->  e' ->
      let fs := prefix ++ (x,(τ,e)) :: suffix in
      let fs' := prefix ++ (x,(τ,e')) :: suffix in
      ℵ ϵ, rec { fs } @ i -->  rec { fs' } @ i
  | step_header (prefix suffix : F.fs string (E.t * E.e tags_t))
                (x : string) (τ : E.t)
                (b e e' : E.e tags_t) (i : tags_t) :
      V.value b ->
      F.predfs_data (V.value ∘ snd) prefix ->
      ℵ ϵ, e -->  e' ->
      let fs := prefix ++ (x,(τ,e)) :: suffix in
      let fs' := prefix ++ (x,(τ,e')) :: suffix in
      ℵ ϵ, hdr { fs } valid:=b @ i -->  hdr { fs' } valid:=b @ i
  | step_header_valid (fs : F.fs string (E.t * E.e tags_t))
                      (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
      ℵ ϵ, hdr { fs } valid:=e @ i -->  hdr { fs } valid:=e' @ i
  | step_header_stack (ts : F.fs string (E.t))
                      (prefix suffix : list (E.e tags_t))
                      (e e' : E.e tags_t) (size : positive)
                      (ni : Z) (i : tags_t) :
      Forall V.value prefix ->
      ℵ ϵ, e -->  e' ->
      let hs := prefix ++ e :: suffix in
      let hs' := prefix ++ e' :: suffix in
      ℵ ϵ, Stack hs:ts[size] nextIndex:=ni @ i -->  Stack hs':ts[size] nextIndex:=ni @ i
  where "'ℵ' ϵ , e1 '-->' e2" := (expr_step ϵ e1 e2).
  (**[]*)

  Reserved Notation "'ℶ' e1 '-->'  e2"
           (at level 40, e1 custom p4expr, e2 custom p4expr).

  Inductive lvalue_step {tags_t : Type} : E.e tags_t -> E.e tags_t -> Prop :=
  | lstep_member (e e' : E.e tags_t) (τ : E.t) (x : string) (i : tags_t) :
      ℶ e -->  e' ->
      ℶ Mem e:τ dot x @ i -->   Mem e':τ dot x @ i
  | lstep_access (e e' : E.e tags_t) (idx : Z) (i : tags_t) :
      ℶ e -->  e' ->
      ℶ Access e[idx] @ i -->   Access e'[idx] @ i
  where "'ℶ' e1 '-->' e2" := (lvalue_step e1 e2).
  (**[]*)

  Reserved Notation "'π' envn , pe1 '-->' pe2"
           (at level 40, pe1 custom p4prsrexpr, pe2 custom p4prsrexpr).

  Inductive step_parser_expr {tags_t : Type} (ϵ : @eenv tags_t)
    : PR.e tags_t -> PR.e tags_t -> Prop :=
  | step_select_discriminee (e e' : E.e tags_t) (d : PR.e tags_t)
                            (cases : F.fs PR.pat (PR.e tags_t)) (i : tags_t) :
      ℵ ϵ, e -->  e' ->
      π ϵ, select e { cases } default:=d @ i-->  select e' { cases } default:=d @ i
  | step_select_resolve (v : E.e tags_t) (d : PR.e tags_t)
                        (cases : F.fs PR.pat (PR.e tags_t)) (i : tags_t) :
      V.value v ->
      let pe := match F.find_value (fun _ => false) cases with (** TODO!! *)
                | None => d
                | Some pe => pe
                end in
      π ϵ, select v { cases } default:=d @ i-->  pe
  where "'π' envn , pe1 '-->' pe2"
          := (step_parser_expr envn pe1 pe2).

  Reserved Notation "'ℸ' cfg , tbls , aa , fns , ins , ϵ1 , k1 '-->' k2 , ϵ2"
           (at level 40, k1 custom p4kstmt, k2 custom p4kstmt,
            ϵ1 custom p4env, ϵ2 custom p4env).
(** TODO: Architecture & Target Issues:
    - Need a general model for architectures & targets that is both:
      + suitably abstract & parameterizable for all levels of compilation.
      + constrained enough to be useful in dynamic semantics.
    - Unsure of how to evaluate externs.
    - Unsure of packet representation.
    - Unsure of how to represent & evaluate pipeline.
    ```p4
    extern packet_in {
        void extract<T>(out T); /// reads from packet into out var
        T lookahead<T>(); /// reads from packet
        void advance(in bit<32>); /// writes to packet cursor
        bit<32> length(); /// reads from packet
    }

    extern packet_out {
           void emit<T>(in T); /// writes to output packet
    }
    ```
    Brain storm: could extern methods just be coq-functions?
    Since they are purely semantic, do I even need a consistent
    representation?

    Perhaps all IRs share some notion of "packet",
    and each IR may deal with extern-representations separately?
 *)

  (** Statement evaluation.
      This continuation-based approach
      is inspired by that of a small-step
      semantics for Cminor.
      [https://www.cs.princeton.edu/~appel/papers/seplogCminor.pdf] *)
  Inductive kstmt_step {tags_t : Type}
            (cfg : @ctrl tags_t) (tbls : @tenv tags_t) (aa : @aenv tags_t)
            (fns : fenv) (ins : @ienv tags_t) (ϵ : eenv) :
    kstmt -> kstmt -> eenv -> Prop :=
  | step_seq (s1 s2 : ST.s tags_t) (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ s1; s2 @ i ⋅ k -->  κ s1 ⋅ κ s2 ⋅ k, ϵ
  | step_skip (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ skip @ i ⋅ k -->  k, ϵ
  | step_block (s : ST.s tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ b{ s }b ⋅ k -->  κ s ⋅ ∫ ϵ ⊗ k, ϵ
  | step_kblock (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, ∫ ϵk ⊗ k -->  k, ϵk ≪ ϵ
  | step_vardecl (τ : E.t) (x : string) (i : tags_t) (k : kstmt) :
      let v := edefault i τ in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ var x : τ @ i ⋅ k -->   k, x ↦ v;; ϵ
  | step_asgn_r (e1 e2 e2' : E.e tags_t) (τ : E.t) (i : tags_t) (k : kstmt) :
      ℵ ϵ, e2 -->  e2' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ asgn e1 := e2:τ @ i ⋅ k -->  κ asgn e1 := e2':τ @ i ⋅ k, ϵ
  | step_asgn_l (e1 e1' v2 : E.e tags_t) (τ : E.t) (i : tags_t) (k : kstmt) :
      V.value v2 ->
      ℶ e1 -->  e1' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ asgn e1 := v2:τ @ i ⋅ k -->  κ asgn e1' := v2:τ @ i ⋅ k, ϵ
  | step_asgn (v1 v2 : E.e tags_t) (τ : E.t) (i : tags_t) (k : kstmt) :
      V.lvalue v1 ->
      V.value v2 ->
      let ϵ' := lv_update v1 v2 ϵ in
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ asgn v1 := v2:τ @ i ⋅ k -->  k, ϵ'
  | step_exit (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ exit @ i ⋅ k -->   EXIT k, ϵ
  | step_kexit_kseq (s : ST.s tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT κ s ⋅ k -->  EXIT k, ϵ
  | step_kexit_kblock (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT ∫ ϵk ⊗ k -->  EXIT k, ϵk ≪ ϵ
  | step_return_void (i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, κ returns @ i ⋅ k -->  VOID k, ϵ
  | step_return_fruit (e e' : E.e tags_t) (τ : E.t) (i : tags_t) (k : kstmt) :
      ℵ ϵ, e -->  e' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ return e:τ @ i ⋅ k -->  κ return e':τ @ i ⋅ k, ϵ
  | step_return_value (v : E.e tags_t) (τ : E.t) (i : tags_t) (k : kstmt) :
      V.value v ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ return v:τ @ i ⋅ k -->  FRUIT v k, ϵ
  | step_kreturn_kseq (o : option (E.e tags_t)) (s : ST.s tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, RETURN o κ s ⋅ k -->  RETURN o k, ϵ
  | step_kreturn_kblock (o : option (E.e tags_t)) (ϵk : eenv) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT ∫ ϵk ⊗ k -->  EXIT k, ϵk ≪ ϵ
  | step_cond (e e' : E.e tags_t) (s1 s2 : ST.s tags_t) (i : tags_t) (k : kstmt) :
      ℵ ϵ, e -->  e' ->
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if e:Bool then s1 else s2 @ i ⋅ k -->
      κ if e:Bool then s1 else s2 @ i ⋅ k, ϵ
  | step_cond_true (s1 s2 : ST.s tags_t) (i' i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if TRUE @ i' :Bool then s1 else s2 @ i ⋅ k -->  κ s1 ⋅ k, ϵ
  | step_cond_false (s1 s2 : ST.s tags_t) (i' i : tags_t) (k : kstmt) :
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ if FALSE @ i' :Bool then s1 else s2 @ i ⋅ k -->  κ s2 ⋅ k, ϵ
  | step_funcall_in_arg (prefix suffix : E.args tags_t) (f x : string)
                        (τ : E.t) (e e' : E.e tags_t)
                        (o : option (E.t * E.e tags_t))
                        (i : tags_t) (k : kstmt) :
      F.predfs_data
        (P.pred_paramarg
           (V.value ∘ snd) (V.lvalue ∘ snd)) prefix ->
      ℵ ϵ, e -->  e' ->
      let args  := prefix ++ (x, P.PAIn (τ,e))  :: suffix in
      let args' := prefix ++ (x, P.PAIn (τ,e')) :: suffix in
      ℸ cfg, tbls, aa, fns, ins, ϵ,
      κ funcall f with args  into o @ i ⋅ k -->
      κ funcall f with args' into o @ i ⋅ k, ϵ
   | step_funcall_lvalue (args : E.args tags_t) (f : string) (τ : E.t)
                         (e e' : E.e tags_t) (i : tags_t) (k : kstmt) :
       F.predfs_data
         (P.pred_paramarg
            (V.value ∘ snd) (V.lvalue ∘ snd)) args ->
       ℶ e -->  e' ->
       ℸ cfg, tbls, aa, fns, ins, ϵ,
       κ let e:τ  := call f with args @ i ⋅ k -->
       κ let e':τ := call f with args @ i ⋅ k, ϵ
   | step_funcall (args : E.args tags_t) (f : string)
                  (o : option (E.t * E.e tags_t))
                  (i : tags_t) (k : kstmt)
                  (body : ST.s tags_t) (fϵ : eenv)
                  (fclosure : fenv) (fins : ienv) :
       lookup fns f = Some (FDecl fϵ fclosure fins body) ->
       predop (V.lvalue ∘ snd) o ->
       F.predfs_data
         (P.pred_paramarg
            (V.value ∘ snd) (V.lvalue ∘ snd)) args ->
       let fϵ' := copy_in args ϵ fϵ in
       let arrow := P.Arrow args o in
       ℸ cfg, tbls, aa, fns, ins, ϵ,
       κ funcall f with args into o @ i ⋅ k -->
       κ body ⋅ Λ (arrow, ϵ) k, fϵ'
   | step_kexit_kcall (ϵk : eenv) (args : E.args tags_t) (k : kstmt) :
       let ϵ' := copy_out args ϵ ϵk in
       let arrow := P.Arrow args None in
       ℸ cfg, tbls, aa, fns, ins, ϵ, EXIT Λ (arrow, ϵk) k -->  k, ϵ'
   | step_void_kcall (ϵk : eenv) (args : E.args tags_t) (k : kstmt) :
       let ϵ' := copy_out args ϵ ϵk in
       let arrow := P.Arrow args None in
       ℸ cfg, tbls, aa, fns, ins, ϵ, VOID Λ (arrow, ϵk) k -->  k, ϵ'
   | step_fruit_kcall (v lv : E.e tags_t) (τ : E.t) (ϵk : eenv)
                      (args : E.args tags_t) (k : kstmt) :
       let ϵ' := ϵk ▷ copy_out args ϵ ▷ lv_update lv v in
       let arrow := P.Arrow args (Some (τ, lv)) in
       ℸ cfg, tbls, aa, fns, ins, ϵ, FRUIT v Λ (arrow, ϵk) k -->  k, ϵ'
  where "'ℸ' cfg , tbls , aa , fns , ins , ϵ1 , k1 '-->' k2 , ϵ2"
          := (kstmt_step cfg tbls aa fns ins ϵ1 k1 k2 ϵ2).
  (**[]*)
End Step.
