Require Export P4cub.Check.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.micromega.Lia.

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
                      (ni : Z) :
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
  Module PT := E.ProperType.

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
        => Some # E.ERecord (combine (F.keys fs) # combine (F.values fs) vs) i
      | {{ hdr { fs } }}, <{ tup vs @ i }>
        => Some # E.EHeader (combine (F.keys fs) # combine (F.values fs) vs) <{ TRUE @ i }> i
      | _, _ => None
      end.
    (**[]*)

    (** Unary Operations. *)
    Definition eval_uop (op : E.uop) (e : E.e tags_t) : option (E.e tags_t) :=
      match op, e with
      | E.Not, <{ BOOL b @ i }>
        => let b' := negb b in Some <{ BOOL b' @ i }>
      | E.BitNot, <{ w W n @ i }>
        => let n' := BitArith.bit_not w n in Some <{ w W n' @ i }>
      | E.BitNot, <{ w S n @ i }>
        => let n' := IntArith.bit_not w n in Some <{ w S n' @ i }>
      | E.UMinus, <{ w W z @ i }>
        => let z' := BitArith.neg w z in Some <{ w W z' @ i }>
      | E.UMinus, <{ w S z @ i }>
        => let z' := IntArith.neg w z in Some <{ w S z' @ i }>
      | _, _ => None
      end.
    (**[]*)

    (** Binary operations. *)
    Definition eval_bop
               (op : E.bop) (v1 v2 : E.e tags_t) (i : tags_t) : option (E.e tags_t) :=
      match op, v1, v2 with
      | E.Plus, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some # E.EBit w (BitArith.plus_mod w n1 n2) i
      | E.Plus, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some # E.EInt w (IntArith.plus_mod w z1 z2) i
      | E.PlusSat, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some # E.EBit w (BitArith.plus_sat w n1 n2) i
      | E.PlusSat,  <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some # E.EInt w (IntArith.plus_sat w z1 z2) i
      | E.Minus, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some # E.EBit w (BitArith.minus_mod w n1 n2) i
      | E.Minus, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some # E.EInt w (IntArith.minus_mod w z1 z2) i
      | E.MinusSat, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some # E.EBit w (BitArith.minus_sat w n1 n2) i
      | E.MinusSat, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some # E.EInt w (IntArith.minus_sat w z1 z2) i
      | E.Shl, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some # E.EBit w (BitArith.shift_left w n1 n2) i
      | E.Shl, <{ w S z1 @ _ }>, <{ _ W z2 @ _ }>
        => Some # E.EInt w (IntArith.shift_left w z1 z2) i
      | E.Shr, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some # E.EBit w (BitArith.shift_right w n1 n2) i
      | E.Shr, <{ w S z1 @ _ }>, <{ _ W z2 @ _ }>
        => Some # E.EInt w (IntArith.shift_right w z1 z2) i
      | E.BitAnd, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some # E.EBit w (BitArith.bit_and w n1 n2) i
      | E.BitAnd, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some # E.EInt w (IntArith.bit_and w z1 z2) i
      | E.BitXor, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some # E.EBit w (BitArith.bit_xor w n1 n2) i
      | E.BitXor, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some # E.EInt w (IntArith.bit_xor w z1 z2) i
      | E.BitOr, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }>
        => Some # E.EBit w (BitArith.bit_or w n1 n2) i
      | E.BitOr, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }>
        => Some # E.EInt w (IntArith.bit_or w z1 z2) i
      | E.Le, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some # E.EBool (n1 <=? n2)%Z i
      | E.Le, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some # E.EBool (z1 <=? z2)%Z i
      | E.Lt, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some # E.EBool (n1 <? n2)%Z i
      | E.Lt, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some # E.EBool (z1 <? z2)%Z i
      | E.Ge, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some # E.EBool (n2 <=? n1)%Z i
      | E.Ge, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some # E.EBool (z2 <=? z1)%Z i
      | E.Gt, <{ w W n1 @ _ }>, <{ _ W n2 @ _ }> => Some # E.EBool (n2 <? n1)%Z i
      | E.Gt, <{ w S z1 @ _ }>, <{ _ S z2 @ _ }> => Some # E.EBool (z2 <? z1)%Z i
      | E.And, <{ BOOL b1 @ _ }>, <{ BOOL b2 @ _ }> => Some # E.EBool (b1 && b2) i
      | E.Or, <{ BOOL b1 @ _ }>, <{ BOOL b2 @ _ }> => Some # E.EBool (b1 || b2) i
      | E.Eq, _, _ => Some # E.EBool (E.ExprEquivalence.eqbe v1 v2) i
      | E.NotEq, _, _ => Some # E.EBool (negb # E.ExprEquivalence.eqbe v1 v2) i
      | E.PlusPlus, <{ w1 W n1 @ _ }>, <{ w2 W n2 @ _ }>
      | E.PlusPlus, <{ w1 W n1 @ _ }>, <{ w2 S n2 @ _ }>
        => Some # E.EBit (w1 + w2)%positive (BitArith.concat w1 w2 n1 n2) i
      | E.PlusPlus, <{ w1 S n1 @ _ }>, <{ w2 S n2 @ _ }>
      | E.PlusPlus, <{ w1 S n1 @ _ }>, <{ w2 W n2 @ _ }>
        => Some # E.EInt (w1 + w2)%positive (IntArith.concat w1 w2 n1 n2) i
      | _, _, _ => None
      end.
    (**[]*)

    (** Get header data from value. *)
    Definition header_data (v : E.e tags_t)
      : option (F.fs string (E.t * E.e tags_t) * bool * tags_t * tags_t) :=
      match v with
      | <{ hdr { fs } valid:= BOOL b @ ib @ i}> => Some (fs,b,ib,i)
      | _ => None
      end.

    (** Get header stack data from value. *)
    Definition header_stack_data (v : E.e tags_t)
      : option (positive * Z *
                F.fs string (E.t) *
                (list (E.e tags_t))) :=
      match v with
      | <{ Stack hs:ts[n] nextIndex:=ni}> => Some (n,ni,ts,hs)
      | _ => None
      end.
    (**[]*)

    (** Header operations. *)
    Definition eval_hdr_op
               (op : E.hdr_op) (fs : F.fs string (E.t * E.e tags_t))
               (b : bool) (i ib : tags_t) : E.e tags_t :=
      match op with
      | E.HOIsValid => <{ BOOL b @ i}>
      | E.HOSetValid => <{ hdr { fs } valid:=TRUE @ ib @ i}>
      | E.HOSetInValid => <{ hdr { fs } valid:=FALSE @ ib @ i }>
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
            E.EHeaderStack tfs hs n 0%Z
      end.
    (**[]*)

    Lemma value_edefault : forall i τ, V.value (edefault i τ).
    Proof.
      Local Hint Constructors V.value : core.
    Admitted.

    (** Header stack operations. *)
    Definition eval_stk_op
               (i : tags_t) (op : E.hdr_stk_op)
               (size : positive) (nextIndex : Z)
               (ts : F.fs string (E.t))
               (hs : list (E.e tags_t))
      : option (E.e tags_t) :=
      let w := 32%positive in
      let sizenat := Pos.to_nat size in
      let hdefault :=
          E.EHeader
            (F.map (fun τ => (τ, edefault i τ)) ts)
          <{ BOOL false @ i }> i in
      match op with
      | E.HSOSize => let s := (Zpos size)%Z in Some <{ w W s @ i }>
      | E.HSONext => nth_error hs # Z.to_nat nextIndex
      | E.HSOPush n
        => let nnat := Pos.to_nat n in
          if lt_dec nnat sizenat then
            let new_hdrs := repeat hdefault nnat in
            let remains := firstn (sizenat - nnat) hs in
            Some # E.EHeaderStack ts (new_hdrs ++ remains) size #
                 Z.min (nextIndex + Zpos n)%Z (Z.pos size - 1)%Z
          else
            let new_hdrs := repeat hdefault sizenat in
            Some # E.EHeaderStack ts new_hdrs size (Z.pos size - 1)%Z
      | E.HSOPop n
        => let nnat := Pos.to_nat n in
          if lt_dec nnat sizenat then
            let new_hdrs := repeat hdefault nnat in
            let remains := skipn nnat hs in
            Some # E.EHeaderStack ts (remains ++ new_hdrs) size #
                 Z.max 0 (nextIndex - Zpos n)%Z
          else
            let new_hdrs := repeat hdefault sizenat in
            Some # E.EHeaderStack ts new_hdrs size 0%N
      end.
    (**[]*)

    Definition eval_member (x : string) (v : E.e tags_t) : option (E.e tags_t) :=
      match v with
      | <{ rec { vs } @ _ }>
      | <{ hdr { vs } valid:=_ @ _ }> => map_option (F.get x vs) snd
      | _                             => None
      end.
    (**[]*)

    Section HelpersType.
      Local Hint Constructors check_expr : core.
      Local Hint Extern 0 => bit_bounded : core.
      Local Hint Extern 0 => int_bounded : core.

      Lemma eval_cast_types : forall errs Γ τ τ' v v',
          eval_cast τ' v = Some v' ->
          proper_cast τ τ' ->
          ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
          ⟦ errs, Γ ⟧ ⊢ v' ∈ τ'.
      Proof.
        intros;
        match goal with
        | HPC: proper_cast _ _,
          HT : ⟦ _, _ ⟧ ⊢  _ ∈ _ |- _
          => inv HPC; inv HT; unravel in *; try discriminate
        end;
        try match goal with
            | H: match ?w with (_~1)%positive | _ => _ end = Some _
              |- _ => destruct w; inv H; try constructor; auto
            | H: (if ?b then _ else _) = Some _ |- _
              => destruct b; inv H; try constructor; auto
            | H: Some _ = Some _ |- _ => inv H; try constructor; auto 2
            end; try (cbv; auto 2; assumption).
        - destruct n; inv H; auto 2.
          destruct p; inv H1; auto 2.
        - generalize dependent fs.
          induction es as [| e es IHes]; intros [| [x τ] fs] H;
          inv H; unravel in *; constructor; try split;
          unravel; try apply IHes; auto 2.
        - apply pn_header. rewrite F.predfs_data_map. assumption.
        - clear H3. generalize dependent fs.
          induction es as [| e es IHes]; intros [| [x τ] fs] H;
          inv H; unravel in *; constructor; try split;
          unravel; try apply IHes; auto 2.
      Qed.

      Lemma eval_uop_types : forall errs Γ op e v τ,
          uop_type op τ -> V.value e -> eval_uop op e = Some v ->
          ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> ⟦ errs, Γ ⟧ ⊢ v ∈ τ.
      Proof.
        intros errs Γ op e v τ Huop Hev Heval Het;
        inv Huop; inv Hev; inv Het; unravel in *; inv Heval; auto 2.
      Qed.

      Lemma eval_bop_types : forall Γ errs op τ1 τ2 τ (i : tags_t) v1 v2 v,
          bop_type op τ1 τ2 τ ->
          V.value v1 -> V.value v2 ->
          eval_bop op v1 v2 i = Some v ->
          ⟦ errs, Γ ⟧ ⊢ v1 ∈ τ1 -> ⟦ errs, Γ ⟧ ⊢ v2 ∈ τ2 -> ⟦ errs, Γ ⟧ ⊢ v ∈ τ.
      Proof.
        intros Γ errs op τ1 τ2 τ v1 v2 v i Hbop Hv1 Hv2 Heval Ht1 Ht2;
        inv Hbop; unravel in *;
        repeat match goal with
               | H: Some _ = Some _ |- _ => inv H; auto
               | H: numeric _ |- _ => inv H
               | H: numeric_width _ _ |- _ => inv H
               | |- _ => inv Hv1; inv Ht1; inv Hv2; inv Ht2
               end; auto 2.
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
        inv Hmem; inv Hv; inv Ht.
        - eapply F.relfs_get_r in H1 as [[? ?] [? ?]]; eauto 2;
          intuition; unravel in *; subst.
          rewrite H0 in Heval; unravel in *; inv Heval; auto 2.
        - eapply F.relfs_get_r in H6 as [[? ?] [? ?]]; eauto 2.
          intuition; unravel in *; subst.
          rewrite H1 in Heval; unravel in *; inv Heval; auto 2.
      Qed.

      Local Hint Constructors proper_nesting : core.
      Hint Rewrite repeat_length.
      Local Hint Resolve proper_inside_header_nesting : core.

      Lemma eval_hdr_op_types : forall errs Γ op ts fs b i ib,
          PT.proper_nesting {{ hdr { ts } }} ->
          F.relfs (fun te τ => fst te = τ /\
                            let e := snd te in
                            ⟦ errs, Γ ⟧ ⊢ e ∈ τ) fs ts ->
          let τ := type_hdr_op op ts in
          let v := eval_hdr_op op fs b i ib in
          ⟦ errs, Γ ⟧ ⊢ v ∈ τ.
      Proof.
        intros; subst τ; subst v; destruct op;
        simpl in *; constructor; auto 2; constructor.
      Qed.

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

      Lemma eval_stk_op_types : forall errs Γ i op n ni ts hs v,
          BitArith.bound 32%positive (Zpos n) ->
          (0 <= ni < Zpos n)%Z ->
          Pos.to_nat n = length hs ->
          PT.proper_nesting {{ stack ts[n] }} ->
          Forall (fun e => ⟦ errs, Γ ⟧ ⊢ e ∈ hdr { ts }) hs ->
          eval_stk_op i op n ni ts hs = Some v ->
          let τ := type_hdr_stk_op op n ts in
          ⟦ errs, Γ ⟧ ⊢ v ∈ τ.
      Proof.
        intros; subst τ; destruct op;
        unravel in *; invert_proper_nesting;
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
        - eapply Forall_nth_error in H4; eauto 1; simpl in *; auto 1.
      Qed.
    End HelpersType.

    Section HelpersExist.
      Lemma eval_cast_exists : forall errs Γ e τ τ',
        V.value e ->
        proper_cast τ τ' ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        exists v, eval_cast τ' e = Some v.
      Proof.
        intros ? ? ? ? ? Hv Hpc Het; inv Hpc; inv Hv; inv Het;
          unravel; simpl in *; eauto 2.
        - destruct b; eauto 2.
        - destruct n; eauto 2; destruct p; eauto 2;
          try (cbv in H0; destruct H0; try destruct p; discriminate).
        - destruct w; eauto 2.
        - destruct w2; eauto 2.
      Qed.

      Lemma eval_uop_exists : forall op errs Γ e τ,
          uop_type op τ -> V.value e -> ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
          exists v, eval_uop op e = Some v.
      Proof.
        intros op errs Γ e τ Hu Hv Het;
        destruct op; inv Hu; inv Hv; inv Het; unravel; eauto.
      Qed.

      Lemma eval_bop_exists : forall errs Γ op τ1 τ2 τ (i : tags_t) v1 v2,
          bop_type op τ1 τ2 τ ->
          V.value v1 -> V.value v2 ->
          ⟦ errs, Γ ⟧ ⊢ v1 ∈ τ1 -> ⟦ errs, Γ ⟧ ⊢ v2 ∈ τ2 ->
          exists v, eval_bop op v1 v2 i = Some v.
      Proof.
        intros errs Γ op τ1 τ2 τ i v1 v2 Hbop Hv1 Hv2 Ht1 Ht2;
        inv Hbop; unravel in *;
        repeat match goal with
               | H: numeric _ |- _ => inv H
               | H: numeric_width _ _ |- _ => inv H
               | |- _ => inv Hv1; inv Ht1; inv Hv2; inv Ht2
               end; eauto 2.
      Qed.

      Lemma eval_stk_op_exists : forall errs Γ i op n ni ts hs,
          BitArith.bound 32%positive (Zpos n) ->
          (0 <= ni < Zpos n)%Z ->
          Pos.to_nat n = length hs ->
          PT.proper_nesting {{ stack ts[n] }} ->
          Forall (fun e => ⟦ errs, Γ ⟧ ⊢ e ∈ hdr { ts }) hs ->
          exists v, eval_stk_op i op n ni ts hs = Some v.
      Proof.
        intros errs Γ i op n ni ts hs Hn Hni Hnhs Hpt H;
        destruct op; unravel; eauto 2.
        - assert (Hnihs : (Z.to_nat ni < length hs)%nat) by lia.
          pose proof nth_error_exists _ _ Hnihs as [v Hnth].
          rewrite Hnth; eauto 2.
        - destruct (lt_dec (Pos.to_nat n0) (Pos.to_nat n)) as [? | ?]; eauto 2.
        - destruct (lt_dec (Pos.to_nat n0) (Pos.to_nat n)) as [? | ?]; eauto 2.
      Qed.

      Lemma eval_member_exists : forall errs Γ x v ts τ τ',
          V.value v ->
          member_type ts τ ->
          F.get x ts = Some τ' ->
          ⟦ errs, Γ ⟧ ⊢ v ∈ τ ->
          exists v', eval_member x v = Some v'.
      Proof.
        intros errs Γ x v ts τ τ' Hv Hmem Hget Ht;
        inv Hmem; inv Hv; inv Ht; unravel.
        - eapply F.relfs_get_r in H1 as [[? ?] [? ?]]; eauto 2.
          intuition; simpl in *; subst.
          rewrite H0; unravel; eauto 2.
        - eapply F.relfs_get_r in H6 as [[? ?] [? ?]]; eauto 2.
          intuition; simpl in *; subst.
          rewrite H1; unravel; eauto 2.
      Qed.
    End HelpersExist.
  End StepDefs.

  Inductive expr_step {tags_t : Type} (ϵ : eenv)
    : E.e tags_t -> E.e tags_t -> Prop :=
  | step_var (x : string) (τ : E.t)
             (i : tags_t) (e : E.e tags_t) :
      ϵ x = Some e ->
      ℵ ϵ ** Var x:τ @ i -->  e
  | step_cast (τ : E.t) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** Cast e:τ @ i -->  Cast e':τ @ i
  | step_cast_eval (τ : E.t) (v v' : E.e tags_t) (i : tags_t) :
      eval_cast τ v = Some v' ->
      V.value v ->
      ℵ ϵ ** Cast v:τ @ i -->  v'
  | step_uop (op : E.uop) (τ : E.t)
             (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** UOP op e:τ @ i -->  UOP op e':τ @ i
  | step_uop_eval (op : E.uop) (τ : E.t)
                  (v v' : E.e tags_t) (i : tags_t) :
      eval_uop op v = Some v' ->
      V.value v ->
      ℵ ϵ ** UOP op v:τ @ i -->  v'
  | step_bop_l (op : E.bop) (τl τr : E.t)
               (el el' er : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** el -->  el' ->
      ℵ ϵ ** BOP el:τl op er:τr @ i -->  BOP el':τl op er:τr @ i
  | step_bop_r (op : E.bop) (τl τr : E.t)
               (vl er er' : E.e tags_t) (i : tags_t) :
      V.value vl ->
      ℵ ϵ ** er -->  er' ->
      ℵ ϵ ** BOP vl:τl op er:τr @ i -->  BOP vl:τl op er':τr @ i
  | step_bop_eval (op : E.bop) (τl τr : E.t)
                  (vv vl vr : E.e tags_t) (i : tags_t) :
      eval_bop op vl vr i = Some vv ->
      V.value vl -> V.value vr ->
      ℵ ϵ ** BOP vl:τl op vr:τr @ i -->  vv
  | step_member (x : string) (τ : E.t)
                (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** Mem e:τ dot x @ i -->  Mem e:τ dot x @ i
  | step_member_eval (x : string) (τ : E.t)
                     (v v' : E.e tags_t) (i : tags_t) :
      eval_member x v = Some v' ->
      V.value v ->
      ℵ ϵ ** Mem v:τ dot x @ i -->  v'
  | step_header_op (op : E.hdr_op) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** HDR_OP op e @ i -->  HDR_OP op e' @ i
  | step_header_op_eval (op : E.hdr_op) (v v' : E.e tags_t) (i : tags_t) :
      V.value v ->
      map_option (header_data v) (uncurry4 # eval_hdr_op op) = Some v' ->
      ℵ ϵ ** HDR_OP op v @ i -->  v'
  | step_stack_op (op : E.hdr_stk_op) (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** STK_OP op e @ i -->  STK_OP op e' @ i
  | step_stack_op_eval (op : E.hdr_stk_op) (v v' : E.e tags_t) (i : tags_t) :
      V.value v ->
      bind_option (header_stack_data v) (uncurry4 # eval_stk_op i op) = Some v' ->
      ℵ ϵ ** STK_OP op v @ i -->  v'
  | step_stack_access (e e' : E.e tags_t) (n : Z) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** Access e[n] @ i -->  Access e'[n] @ i
  | step_stack_access_eval (v v' : E.e tags_t) (n : Z) (i : tags_t) :
      bind_option
        (map_option (header_stack_data v) fourple_4)
        (fun hs => nth_error hs (Z.to_nat n)) = Some v' ->
      V.value v ->
      ℵ ϵ ** Access v[n] @ i -->  v'
  | step_tuple (prefix suffix : list (E.e tags_t))
               (e e' : E.e tags_t) (i : tags_t) :
      Forall V.value prefix ->
      ℵ ϵ ** e -->  e' ->
      let es := prefix ++ e :: suffix in
      let es' := prefix ++ e' :: suffix in
      ℵ ϵ ** tup es @ i -->  tup es' @ i
  | step_record (prefix suffix : F.fs string (E.t * E.e tags_t))
                (x : string) (τ : E.t)
                (e e' : E.e tags_t) (i : tags_t) :
      F.predfs_data (V.value ∘ snd) prefix ->
      ℵ ϵ ** e -->  e' ->
      let fs := prefix ++ (x,(τ,e)) :: suffix in
      let fs' := prefix ++ (x,(τ,e')) :: suffix in
      ℵ ϵ ** rec { fs } @ i -->  rec { fs' } @ i
  | step_header (prefix suffix : F.fs string (E.t * E.e tags_t))
                (x : string) (τ : E.t)
                (b e e' : E.e tags_t) (i : tags_t) :
      V.value b ->
      F.predfs_data (V.value ∘ snd) prefix ->
      ℵ ϵ ** e -->  e' ->
      let fs := prefix ++ (x,(τ,e)) :: suffix in
      let fs' := prefix ++ (x,(τ,e')) :: suffix in
      ℵ ϵ ** hdr { fs } valid:=b @ i -->  hdr { fs' } valid:=b @ i
  | step_header_valid (fs : F.fs string (E.t * E.e tags_t))
                      (e e' : E.e tags_t) (i : tags_t) :
      ℵ ϵ ** e -->  e' ->
      ℵ ϵ ** hdr { fs } valid:=e @ i -->  hdr { fs } valid:=e' @ i
  | step_header_stack (ts : F.fs string (E.t))
                      (prefix suffix : list (E.e tags_t))
                      (e e' : E.e tags_t) (size : positive)
                      (ni : Z) :
      Forall V.value prefix ->
      ℵ ϵ ** e -->  e' ->
      let hs := prefix ++ e :: suffix in
      let hs' := prefix ++ e' :: suffix in
      ℵ ϵ ** Stack hs:ts[size] nextIndex:=ni -->  Stack hs':ts[size] nextIndex:=ni
  where "'ℵ' ϵ '**' e1 '-->' e2" := (expr_step ϵ e1 e2).
End Step.
