Set Warnings "-custom-entry-overridden".
Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt Poulet4.P4Arith
        Poulet4.P4cub.Syntax.AST Poulet4.P4cub.Syntax.IndPrincip.

Reserved Notation "∮ e1 ≡ e2"
         (at level 200, e1 custom p4expr, e2 custom p4expr, no associativity).

Module P := P4cub.
Module F := P.F.
Module E := P.Expr.

Module TypeEquivalence.
  Import Field.FieldTactics E TypeNotations.
  
  Section TypeEquivalence.
    (** Decidable equality. *)
    Fixpoint eqbt (τ1 τ2 : t) : bool :=
      let fix lstruct (ts1 ts2 : list t) : bool :=
          match ts1, ts2 with
          | [], [] => true
          | t1::ts1, t2::ts2 => eqbt t1 t2 && lstruct ts1 ts2
          | [], _::_ | _::_, [] => false
          end in
      let fix fstruct (ts1 ts2 : F.fs string t) : bool :=
          match ts1, ts2 with
          | [], [] => true
          | (x1,t1)::ts1, (x2,t2)::ts2
            => equiv_dec x1 x2 &&&& eqbt t1 t2 && fstruct ts1 ts2
          | [], _::_ | _::_, [] => false
          end in
      match τ1, τ2 with
      | {{ Bool }}, {{ Bool }}
      | {{ error }}, {{ error }}
      | {{ matchkind }}, {{ matchkind }} => true
      | {{ bit<w1> }}, {{ bit<w2> }}
      | {{ int<w1> }}, {{ int<w2> }} => (w1 =? w2)%positive
      | {{ tuple ts1 }}, {{ tuple ts2 }} => lstruct ts1 ts2
      | {{ hdr { ts1 } }}, {{ hdr { ts2 } }}
      | {{ struct { ts1 } }}, {{ struct { ts2 } }} => fstruct ts1 ts2
      | {{ stack ts1[n1] }}, {{ stack ts2[n2] }}
        => (n1 =? n2)%positive && fstruct ts1 ts2
      | _, _ => false
      end.
    (**[]*)
    
    Lemma eqbt_refl : forall τ, eqbt τ τ = true.
    Proof.
      Hint Rewrite Pos.eqb_refl.
      Hint Rewrite equiv_dec_refl.
      Hint Extern 0 => equiv_dec_refl_tactic : core.
      induction τ using custom_t_ind; unravel;
        autorewrite with core; auto;
          try ind_list_Forall; try ind_list_predfs;
            intuition; autorewrite with core;
              repeat (rewrite_true; unravel); auto.
    Qed.
    
    Ltac eauto_too_dumb :=
      match goal with
      | H: ?f ?x ?y = ?z,
           IH: (forall y, ?f ?x y = ?z -> _)
        |- _ => apply IH in H; clear IH
      end.
    
    Lemma eqbt_eq : forall t1 t2, eqbt t1 t2 = true -> t1 = t2.
    Proof.
      Hint Resolve Peqb_true_eq : core.
      Hint Extern 5 =>
      match goal with
      | H: (_ =? _)%positive = true
        |- _ => apply Peqb_true_eq in H; subst; auto
      end : core.
      induction t1 using custom_t_ind; intros []; intros; unravel in *;
        try discriminate; repeat destruct_andb; auto; f_equal;
          try match goal with
              | IH: Forall _ ?ts1,
                    H: _ ?ts1 ?ts2 = true
                |- _ => generalize dependent ts2;
                        induction ts1; intros []; intros;
                          try discriminate; try inv_Forall_cons;
                            repeat destruct_andb; intuition;
                              repeat eauto_too_dumb; subst; auto
              end;
          try match goal with
              | IH: F.predfs_data _ ?ts1,
                    H: _ ?ts1 ?ts2 = true
                |- _ => generalize dependent ts2;
                        induction ts1; intros [| [? ?] ?]; intros;
                          try discriminate; try invert_cons_predfs;
                            try destruct_lifted_andb;
                            repeat destruct_andb; intuition;
                              unfold equiv in *; subst;
                                repeat eauto_too_dumb; subst; auto
              end.
    Qed.
    
    Lemma eqbt_eq_iff : forall t1 t2 : t,
        eqbt t1 t2 = true <-> t1 = t2.
    Proof.
      Hint Resolve eqbt_refl : core.
      Hint Resolve eqbt_eq : core.
      intros t1 t2; split; intros; subst; auto.
    Qed.
    
    Lemma eqbt_reflect : forall t1 t2, reflect (t1 = t2) (eqbt t1 t2).
    Proof.
      Hint Resolve eqbt_eq_iff : core.
      intros; reflect_split; auto.
      apply eqbt_eq_iff in H;
        rewrite H in Heqb; discriminate.
    Defined.
    
    Transparent eqbt_reflect.

    Lemma eq_dec : forall t1 t2 : t,
        t1 = t2 \/ t1 <> t2.
    Proof.
      intros t1 t2. pose proof eqbt_reflect t1 t2 as H.
      inv H; auto.
    Qed.
  End TypeEquivalence.
  
  Instance TypeEqDec : EqDec t eq :=
    { equiv_dec := fun t1 t2 => reflect_dec _ _ (eqbt_reflect t1 t2) }.
  (**[]*)
End TypeEquivalence.

(** Decidable Expression Equivalence. *)
Module ExprEquivalence.
  Import Field.FieldTactics E
         TypeNotations UopNotations BopNotations
         MatchkindNotations ExprNotations TypeEquivalence.
  
  Instance UopEqDec : EqDec uop eq.
  Proof.
    intros [] []; unravel in *;
      try match goal with
          | n1 : positive, n2: positive
            |- _ => destruct (Pos.eq_dec n1 n2) as [? | ?]; subst; auto
          end; auto 2;
        try (right; intros ?; try discriminate;
             inv_eq; try contradiction).
  Defined.
  
  Instance BopEqDec : EqDec bop eq.
  Proof.
    intros [] []; unfold equiv, complement in *;
      auto 2; right; intros ?; discriminate.
  Defined.
  
  (** Equality of expressions. *)
  Inductive equive {tags_t : Type} : e tags_t -> e tags_t -> Prop :=
  | equive_bool b i i' :
      ∮ BOOL b @ i ≡ BOOL b @ i'
  | equive_bit w n i i' :
      ∮ w W n @ i ≡ w W n @ i'
  | equive_int w z i i' :
      ∮ w S z @ i ≡ w S z @ i'
  | equive_var x τ i1 i2 :
      ∮ Var x:τ @ i1 ≡ Var x:τ @ i2
  | equive_slice e1 e2 τ h l i1 i2 :
      ∮ e1 ≡ e2 ->
      ∮ Slice e1:τ [h:l] @ i1 ≡ Slice e2:τ [h:l] @ i2
  | equive_cast τ e1 e2 i1 i2 :
      ∮ e1 ≡ e2 ->
      ∮ Cast e1:τ @ i1 ≡ Cast e2:τ @ i2
  | equive_uop op τ e1 e2 i1 i2 :
      ∮ e1 ≡ e2 ->
      ∮ UOP op e1:τ @ i1 ≡ UOP op e2:τ @ i2
  | equive_bop op τl τr el1 er1 el2 er2 i1 i2 :
      ∮ el1 ≡ el2 ->
      ∮ er1 ≡ er2 ->
      ∮ BOP el1:τl op er1:τr @ i1 ≡ BOP el2:τl op er2:τr @ i2
  | equive_tuple es1 es2 i1 i2 :
      Forall2 equive es1 es2 ->
      ∮ tup es1 @ i1 ≡ tup es2 @ i2
  | equive_struct fs1 fs2 i1 i2 :
      F.relfs
        (fun et1 et2 =>
           let τ1 := fst et1 in
           let τ2 := fst et2 in
           let e1 := snd et1 in
           let e2 := snd et2 in
           τ1 = τ2 /\ ∮ e1 ≡ e2) fs1 fs2 ->
      ∮ struct { fs1 } @ i1 ≡ struct { fs2 } @ i2
  | equive_header fs1 fs2 e1 e2 i1 i2 :
      F.relfs
        (fun et1 et2 =>
           let τ1 := fst et1 in
           let τ2 := fst et2 in
           let e1 := snd et1 in
           let e2 := snd et2 in
           τ1 = τ2 /\ ∮ e1 ≡ e2) fs1 fs2 ->
      ∮ e1 ≡ e2 ->
      ∮ hdr { fs1 } valid:=e1 @ i1 ≡ hdr { fs2 } valid:=e2 @ i2
  | equive_member x τ e1 e2 i1 i2 :
      ∮ e1 ≡ e2 ->
      ∮ Mem e1:τ dot x @ i1 ≡ Mem e2:τ dot x @ i2
  | equive_error err i1 i2 :
      ∮ Error err @ i1 ≡ Error err @ i2
  | equive_matchkind mk i1 i2 :
      ∮ Matchkind mk @ i1 ≡ Matchkind mk @ i2
  | equive_header_stack ts hs1 hs2 n ni i1 i2 :
      Forall2 equive hs1 hs2 ->
      ∮ Stack hs1:ts[n] nextIndex:=ni @ i1 ≡ Stack hs2:ts[n] nextIndex:=ni @ i2
  | equive_stack_access e1 e2 n i1 i2 :
      ∮ e1 ≡ e2 ->
      ∮ Access e1[n] @ i1 ≡ Access e2[n] @ i2
  where "∮ e1 ≡ e2" := (equive e1 e2).
  
  (** Induction principle. *)
  Section ExprEquivalenceInduction.
    Variable tags_t : Type.
    
    Variable P : e tags_t -> e tags_t -> Prop.
    
    Hypothesis HBool : forall b i i', P <{ BOOL b @ i }> <{ BOOL b @ i' }>.
    
    Hypothesis HBit : forall w n i i', P <{ w W n @ i }> <{ w W n @ i' }>.
    
    Hypothesis HInt : forall w z i i', P <{ w S z @ i }> <{ w S z @ i' }>.
    
    Hypothesis HVar : forall x τ i1 i2,
        P <{ Var x:τ @ i1 }> <{ Var x:τ @ i2 }>.
    
    Hypothesis HSlice : forall e1 e2 τ h l i1 i2,
        ∮ e1 ≡ e2 ->
        P e1 e2 ->
        P <{ Slice e1:τ [h:l] @ i1 }> <{ Slice e2:τ [h:l] @ i2 }>.
    
    Hypothesis HCast : forall τ e1 e2 i1 i2,
        ∮ e1 ≡ e2 ->
        P e1 e2 ->
        P <{ Cast e1:τ @ i1 }> <{ Cast e2:τ @ i2 }>.
    
    Hypothesis HUop : forall op τ e1 e2 i1 i2,
        ∮ e1 ≡ e2 ->
        P e1 e2 ->
        P <{ UOP op e1:τ @ i1 }> <{ UOP op e2:τ @ i2 }>.
    
    Hypothesis HBop : forall op τl τr el1 er1 el2 er2 i1 i2,
        ∮ el1 ≡ el2 ->
        P el1 el2 ->
        ∮ er1 ≡ er2 ->
        P er1 er2 ->
        P <{ BOP el1:τl op er1:τr @ i1 }> <{ BOP el2:τl op er2:τr @ i2 }>.
    
    Hypothesis HTup : forall es1 es2 i1 i2,
        Forall2 equive es1 es2 ->
        Forall2 P es1 es2 ->
        P <{ tup es1 @ i1 }> <{ tup es2 @ i2 }>.
    
    Hypothesis HStruct : forall  fs1 fs2 i1 i2,
        F.relfs
          (fun et1 et2 =>
             let τ1 := fst et1 in
             let τ2 := fst et2 in
             let e1 := snd et1 in
             let e2 := snd et2 in
             τ1 = τ2 /\ ∮ e1 ≡ e2) fs1 fs2 ->
        F.relfs
          (fun et1 et2 =>
             let e1 := snd et1 in
             let e2 := snd et2 in
             P e1 e2) fs1 fs2 ->
        P <{ struct { fs1 } @ i1 }> <{ struct { fs2 } @ i2 }>.
    
    Hypothesis HHeader : forall  fs1 fs2 e1 e2 i1 i2,
        F.relfs
          (fun et1 et2 =>
             let τ1 := fst et1 in
             let τ2 := fst et2 in
             let e1 := snd et1 in
             let e2 := snd et2 in
             τ1 = τ2 /\ ∮ e1 ≡ e2) fs1 fs2 ->
        F.relfs
          (fun et1 et2 =>
             let e1 := snd et1 in
             let e2 := snd et2 in
             P e1 e2) fs1 fs2 ->
        ∮ e1 ≡ e2 ->
        P e1 e2 ->
        P <{ hdr { fs1 } valid:=e1 @ i1 }> <{ hdr { fs2 } valid:=e2 @ i2 }>.
    
    Hypothesis HMember : forall x τ e1 e2 i1 i2,
        ∮ e1 ≡ e2 ->
        P e1 e2 ->
        P <{ Mem e1:τ dot x @ i1 }> <{ Mem e2:τ dot x @ i2 }>.
    
    Hypothesis HError : forall err i1 i2,
        P <{ Error err @ i1 }> <{ Error err @ i2 }>.
    
    Hypothesis HMatchkind : forall mk i1 i2,
        P <{ Matchkind mk @ i1 }> <{ Matchkind mk @ i2 }>.
    
    Hypothesis HHeaderStack : forall ts hs1 hs2 n ni i1 i2,
        Forall2 equive hs1 hs2 ->
        Forall2 P hs1 hs2 ->
        P <{ Stack hs1:ts[n] nextIndex:=ni @ i1 }>
        <{ Stack hs2:ts[n] nextIndex:=ni @ i2 }>.
    
    Hypothesis HAccess : forall e1 e2 n i1 i2,
        ∮ e1 ≡ e2 ->
        P e1 e2 ->
        P <{ Access e1[n] @ i1 }> <{ Access e2[n] @ i2 }>.
    
    (** Custom induction principle. *)
    Definition custom_equive_ind :
      forall (e1 e2 : e tags_t), ∮ e1 ≡ e2 -> P e1 e2 :=
      fix eeind e1 e2 (H : ∮ e1 ≡ e2) : P e1 e2 :=
        let fix lind {es1 es2 : list (e tags_t)}
                (Hes : Forall2 equive es1 es2) : Forall2 P es1 es2 :=
            match Hes with
            | Forall2_nil _ => Forall2_nil _
            | Forall2_cons _ _ Hh Ht
              => Forall2_cons _ _ (eeind _ _ Hh) (lind Ht)
            end in
        let fix fsind {fs1 fs2 : F.fs string (t * e tags_t)}
                (Hfs : F.relfs
                         (fun et1 et2 =>
                            let τ1 := fst et1 in
                            let τ2 := fst et2 in
                            let e1 := snd et1 in
                            let e2 := snd et2 in
                            τ1 = τ2 /\ ∮ e1 ≡ e2) fs1 fs2)
            : F.relfs
                (fun et1 et2 =>
                   let e1 := snd et1 in
                   let e2 := snd et2 in
                   P e1 e2) fs1 fs2 :=
            match Hfs with
            | Forall2_nil _ => Forall2_nil _
            | Forall2_cons _ _ (conj Hx (conj _ He)) Ht
              => Forall2_cons _ _
                             (conj Hx (eeind _ _ He)) (fsind Ht)
            end in
        match H with
        | equive_bool b i i' => HBool b i i'
        | equive_bit w n i i' => HBit w n i i'
        | equive_int w z i i' => HInt w z i i'
        | equive_var x τ i1 i2 => HVar x τ i1 i2
        | equive_slice _ _ _ h l i1 i2 He
          => HSlice _ _ _ h l i1 i2 He (eeind _ _ He)
        | equive_cast τ _ _ i1 i2 He
          => HCast τ _ _ i1 i2 He (eeind _ _ He)
        | equive_uop op τ _ _ i1 i2 He
          => HUop op τ _ _ i1 i2 He (eeind _ _ He)
        | equive_bop op tl tr _ _ _ _ i1 i2 Hel Her
          => HBop
              op tl tr _ _ _ _ i1 i2
              Hel (eeind _ _ Hel)
              Her (eeind _ _ Her)
        | equive_tuple _ _ i1 i2 Hes
          => HTup _ _ i1 i2 Hes (lind Hes)
        | equive_struct _ _ i1 i2 Hfs
          => HStruct _ _ i1 i2 Hfs (fsind Hfs)
        | equive_header _ _ _ _ i1 i2 Hfs He
          => HHeader _ _ _ _ i1 i2 Hfs (fsind Hfs) He (eeind _ _ He)
        | equive_member x τ _ _ i1 i2 He
          => HMember x τ _ _ i1 i2 He (eeind _ _ He)
        | equive_error err i1 i2 => HError err i1 i2
        | equive_matchkind mk i1 i2 => HMatchkind mk i1 i2
        | equive_header_stack ts _ _ n ni i1 i2 Hhs
          => HHeaderStack ts _ _ n ni i1 i2 Hhs (lind Hhs)
        | equive_stack_access _ _ n i1 i2 He
          => HAccess _ _ n i1 i2 He (eeind _ _ He)
        end.
    (**[]*)
  End ExprEquivalenceInduction.
  
  Section ExprEquivalenceDefs.
    Context {tags_t : Type}.
    
    Lemma equive_reflexive : Reflexive (@equive tags_t).
    Proof.
      unfold Reflexive; intros e;
        induction e using custom_e_ind;
        econstructor; eauto 2; try reflexivity;
          try (ind_list_Forall; eauto 3; assumption);
          try (ind_list_predfs; constructor;
               repeat split; unravel in *; intuition).
    Qed.
    
    Lemma equive_symmetric : Symmetric (@equive tags_t).
    Proof.
      intros ? ? ?;
             match goal with
             | H: ∮ _ ≡ _ |- _ => induction H using custom_equive_ind
             end;
        econstructor; eauto 1; try (symmetry; assumption);
          try match goal with
              | H: Forall2 equive ?es1 ?es2,
                   IH: Forall2 _ ?es1 ?es2
                |- Forall2 equive ?es2 ?es1
                => induction H; inv IH; constructor; intuition
              end;
          try match goal with
              | H: F.relfs
                     (fun et1 et2 : t * e tags_t =>
                        let τ1 := fst et1 in
                        let τ2 := fst et2 in
                        let e1 := snd et1 in
                        let e2 := snd et2 in
                        τ1 = τ2 /\ (∮ e1 ≡ e2))
                     ?fs1 ?fs2,
                   IH: F.relfs _ ?fs1 ?fs2 |- F.relfs _ ?fs2 ?fs1
                => induction H; inv IH;
                    constructor; repeat relf_destruct;
                      unfold equiv in *; subst;
                        repeat split; intuition
              end.
    Qed.
    
    Lemma equive_transitive : Transitive (@equive tags_t).
    Proof.
      intros e1; induction e1 using custom_e_ind;
        intros ? ? H12 H23; inv H12; inv H23;
          econstructor; try (etransitivity; eassumption); eauto 2;
            try match goal with
                | H: Forall _ ?l1,
                     H12: Forall2 equive ?l1 ?l2,
                          H23: Forall2 equive ?l2 ?l3
                  |- Forall2 equive ?l1 ?l3
                  => generalize dependent l3;
                      generalize dependent l2; induction H;
                        intros [| ? ?] ? [| ? ?] ?;
                               repeat match goal with
                                      | H: Forall2 _ _ (_ :: _) |- _ => inv H
                                      | H: Forall2 _ (_ :: _) _ |- _ => inv H
                                      end; constructor; eauto
                end;
            try match goal with
                | H: F.predfs_data _ ?f1,
                     H12: F.relfs _ ?f1 ?f2,
                          H23: F.relfs _ ?f2 ?f3 |- _
                  => generalize dependent f3;
                      generalize dependent f2; induction H;
                        intros [| [? [? ?]] ?] ? [| [? [? ?]] ?] ?;
                               try match goal with
                                   | H: F.predf_data _ ?x |- _ => destruct x as [? [? ?]]
                                   end;
                        repeat match goal with
                               | H: F.relfs _ _ (_ :: _) |- _ => inv H
                               | H: F.relfs _ (_ :: _) _ |- _ => inv H
                               end; constructor;
                          repeat relf_destruct; unravel in *; intuition;
                            repeat split; unravel; intuition; eauto 2;
                              try match goal with
                                  | IH: forall _, _ -> forall _, _ -> _ |- _ => eapply IH; eauto 1
                                  end; etransitivity; eauto 1
                end.
    Qed.
    
    (** Decidable Expression Equivalence. *)
    Fixpoint eqbe (e1 e2 : e tags_t) : bool :=
      let fix lstruct (es1 es2 : list (e tags_t)) : bool :=
          match es1, es2 with
          | [], _::_ | _::_, [] => false
          | [], [] => true
          | e1::es1, e2::es2 => eqbe e1 e2 && lstruct es1 es2
          end in
      let fix efsstruct {A : Type} (feq : A -> A -> bool)
              (fs1 fs2 : F.fs string (A * e tags_t)) : bool :=
          match fs1, fs2 with
          | [], _::_ | _::_, [] => false
          | [], [] => true
          | (x1, (a1, e1))::fs1, (x2, (a2, e2))::fs2
            => equiv_dec x1 x2 &&&& feq a1 a2 &&
              eqbe e1 e2 && efsstruct feq fs1 fs2
          end in
      match e1, e2 with
      | <{ BOOL b1 @ _ }>, <{ BOOL b2 @ _ }> => eqb b1 b2
      | <{ w1 W n1 @ _ }>, <{ w2 W n2 @ _ }>
        => (w1 =? w2)%positive && (n1 =? n2)%Z
      | <{ w1 S z1 @ _ }>, <{ w2 S z2 @ _ }>
        => (w1 =? w2)%positive && (z1 =? z2)%Z
      | <{ Var x1:τ1 @ _ }>, <{ Var x2:τ2 @ _ }>
        => equiv_dec x1 x2 &&&& eqbt τ1 τ2
      | <{ Slice e1:t1 [h1:l1] @ _ }>, <{ Slice e2:t2 [h2:l2] @ _ }>
        => (h1 =? h2)%positive && (l1 =? l2)%positive &&
          eqbt t1 t2 && eqbe e1 e2
      | <{ Cast e1:τ1 @ _ }>, <{ Cast e2:τ2 @ _ }>
        => eqbt τ1 τ2 && eqbe e1 e2
      | <{ UOP u1 e1:τ1 @ _ }>, <{ UOP u2 e2:τ2 @ _ }>
        => equiv_dec u1 u2 &&&& eqbt τ1 τ2 && eqbe e1 e2
      | <{ BOP el1:τl1 o1 er1:τr1 @ _ }>,
        <{ BOP el2:τl2 o2 er2:τr2 @ _ }>
        => equiv_dec o1 o2 &&&& eqbt τl1 τl2 && eqbt τr1 τr2
          && eqbe el1 el2 && eqbe er1 er2
      | <{ tup es1 @ _ }>, <{ tup es2 @ _ }> => lstruct es1 es2
      | <{ struct { fs1 } @ _ }>, <{ struct { fs2 } @ _ }>
        => efsstruct eqbt fs1 fs2
      | <{ hdr { fs1 } valid:=e1 @ _ }>,
        <{ hdr { fs2 } valid:=e2 @ _ }>
        => eqbe e1 e2 && efsstruct eqbt fs1 fs2
      | <{ Mem e1:τ1 dot x1 @ _ }>, <{ Mem e2:τ2 dot x2 @ _ }>
        => equiv_dec x1 x2 &&&& eqbt τ1 τ2 && eqbe e1 e2
      | <{ Error err1 @ _ }>, <{ Error err2 @ _ }>
        => if equiv_dec err1 err2 then true else false
      | <{ Matchkind mk1 @ _ }>, <{ Matchkind mk2 @ _ }>
        => if equiv_dec mk1 mk2 then true else false
      | <{ Stack hs1:ts1[n1] nextIndex:=ni1 @ _ }>,
        <{ Stack hs2:ts2[n2] nextIndex:=ni2 @ _ }>
        => (n1 =? n2)%positive && (ni1 =? ni2)%Z &&
          F.eqb_fs eqbt ts1 ts2 && lstruct hs1 hs2
      | <{ Access hs1[n1] @ _ }>,
        <{ Access hs2[n2] @ _ }> => (n1 =? n2)%Z && eqbe hs1 hs2
      | _, _ => false
      end.
    (**[]*)
    
    Import F.RelfEquiv.
    
    Hint Rewrite eqb_reflx.
    Hint Rewrite Pos.eqb_refl.
    Hint Rewrite Z.eqb_refl.
    Hint Rewrite eqbt_refl.
    Hint Rewrite equiv_dec_refl.
    Local Hint Extern 5 => equiv_dec_refl_tactic : core.
    Hint Rewrite (@relop_eq string).
    
    (* TODO: somehow using a hidden axiom as an assumption. *)
    Lemma equive_eqbe : forall e1 e2 : e tags_t,
        ∮ e1 ≡ e2 -> eqbe e1 e2 = true.
    Proof.
      intros ? ? ?;
             match goal with
             | H: ∮ _ ≡ _ |- _ => induction H using custom_equive_ind
             end; unravel in *; autorewrite with core; auto 1;
        repeat match goal with
               | H: ?trm = true |- context [ ?trm ] => rewrite H; clear H
               end; auto 1;
          try match goal with
              | H: Forall2 equive ?es1 ?es2,
                   IH: Forall2 _ ?es1 ?es2 |- _
                => induction H; inv IH; unravel in *; auto 1; intuition
              end;
          try match goal with
              | H: F.relfs _ ?fs1 ?fs2,
                   IH: F.relfs _ ?fs1 ?fs2 |- _
                => induction H; inv IH; auto 1;
                    match goal with
                    | H: F.relf _ ?f1 ?f2 |- _
                      => destruct f1 as [? [? ?]];
                          destruct f2 as [? [? ?]];
                          repeat relf_destruct; unravel in *;
                            unfold equiv in *;
                            intuition; subst;
                              autorewrite with core;
                              try equiv_dec_refl_tactic
                    end
              end;
          repeat match goal with
                 | H: ?trm = true |- context [ ?trm ] => rewrite H; clear H
                 end; auto 1;
            try match goal with
                | |- context [ F.eqb_fs eqbt ?ts ?ts ]
                  => rewrite (equiv_eqb_fs _ _ eqbt_reflect ts ts);
                      unfold equiv in *; auto 1; try reflexivity
                end;
            try (equiv_dec_refl_tactic; auto 1;
                 autorewrite with core in *; contradiction).
    Qed.
    
    Ltac eq_true_terms :=
      match goal with
      | H: eqb _ _ = true |- _
        => apply eqb_prop in H; subst
      | H: (_ =? _)%positive = true |- _
        => apply Peqb_true_eq in H; subst
      | H: (_ =? _)%Z = true |- _
        => apply Z.eqb_eq in H; subst
      | H: _ && _ = true |- _
        => apply andb_true_iff in H as [? ?]
      | H: context [equiv_dec ?x1 ?x2 &&&& _] |- _
        => destruct (equiv_dec x1 x2) as [? | ?];
          unravel in H; try discriminate
      | H: context [if equiv_dec ?t1 ?t2 then _ else _] |- _
        => destruct (equiv_dec t1 t2) as [? | ?];
          unravel in H; try discriminate
      | H: context [if eqbt ?t1 ?t2 then _ else _] |- _
        => destruct (eqbt t1 t2) eqn:?;
                   unravel in H; try discriminate
      | H: context [eqbt ?t1 ?t2 && _] |- _
        => destruct (eqbt t1 t2) eqn:?;
                   unravel in H; try discriminate
      | H: context [eqbe ?e1 ?e2 && _] |- _
        => destruct (eqbe e1 e2) eqn:?;
                   unravel in H; try discriminate
      | H: eqbt _ _ = true |- _
        => apply eqbt_eq_iff in H
      | H: context [if eqbe ?e1 ?e2 then _ else _] |- _
        => destruct (eqbe e1 e2) eqn:?;
                   unravel in H; try discriminate
      | H: eqbe ?e1 _ = true,
           IH: forall e2, eqbe ?e1 e2 = true -> ∮ ?e1 ≡ e2 |- _
        => apply IH in H
      | H: _ === _ |- _ => unfold equiv in H;
                         match goal with
                         | H: _ = _ |- _ => subst
                         end
      | H: equiv _ _ |- _ => unfold equiv in H;
                           match goal with
                           | H: _ = _ |- _ => subst
                           end
      | H: Forall _ (_ :: _) |- _ => inv H
      | H: ?P, IH: ?P -> ?Q |- _ => apply IH in H as ?
      | H: (if ?trm then true else false) = true |- _
        => destruct trm eqn:?; unravel in H; try discriminate
      | H: relop _ _ _ |- _ => inv H
      | H: F.eqb_fs eqbt _ _ = true
        |- _ => pose proof eqb_fs_equiv _ _ eqbt_reflect _ _ H as ?; clear H
      | H: F.relfs eq _ _ |- _ => apply eq_relfs in H; subst
      end.
    (**[]*)
    
    Local Hint Constructors equive : core.
    Local Hint Extern 5 => eq_true_terms : core.
    
    Lemma eqbe_equive : forall e1 e2 : e tags_t,
        eqbe e1 e2 = true -> equive e1 e2.
    Proof.
      induction e1 using custom_e_ind;
        intros [] ?; unravel in *;
        try discriminate; auto 1;
          repeat eq_true_terms;
          unfold equiv in *;
          subst; auto; constructor; auto 1;
            try match goal with
                | |- Forall2 _ ?es1 ?es2
                  => generalize dependent es2;
                      induction es1; intros [];
                        unravel in *; try discriminate; auto 5
                end;
            try match goal with
                | |- F.relfs _ ?fs1 ?fs2
                  => generalize dependent fs2;
                      induction fs1 as [| [? [? ?]] ? ?];
                      intros [| [? [? ?]] ?]; intros;
                        unravel in *; try discriminate; auto 1;
                          try destruct_lifted_andb; repeat destruct_andb;
                            try invert_cons_predfs; repeat constructor;
                              intuition; unfold F.relfs in *; auto 2
                end.
    Qed.
    
    Local Hint Resolve equive_eqbe : core.
    Local Hint Resolve eqbe_equive : core.
    
    Lemma equive_eqbe_iff : forall e1 e2 : e tags_t,
        ∮ e1 ≡ e2 <-> eqbe e1 e2 = true.
    Proof. intros; split; auto 2. Qed.
    
    Hint Resolve equive_eqbe_iff : core.
    Hint Extern 5 =>
    match goal with
    | H: eqbe ?e1 ?e2 = false,
         H': ∮ ?e1 ≡ ?e2 |- False
      => apply equive_eqbe_iff in H';
  rewrite H' in H; discriminate
    end : core.
    
    Lemma equive_reflect : forall e1 e2 : e tags_t,
        reflect (∮ e1 ≡ e2) (eqbe e1 e2).
    Proof.
      intros; reflect_split; auto 2;
        autorewrite with core; auto 2.
    Qed.
  End ExprEquivalenceDefs.
  
  Local Hint Resolve equive_reflexive : core.
  Local Hint Resolve equive_symmetric : core.
  Local Hint Resolve equive_transitive : core.
  
  Instance ExprEquiv {tags_t : Type} : Equivalence (@equive tags_t).
  Proof. constructor; auto 1. Defined.
  
  Instance ExprEqDec {tags_t : Type} : EqDec (e tags_t) equive :=
    { equiv_dec := fun e1 e2 => reflect_dec _ _ (equive_reflect e1 e2) }.
  (**[]*)
End ExprEquivalence.
