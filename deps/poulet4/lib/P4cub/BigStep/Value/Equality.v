Require Import Poulet4.P4cub.BigStep.Value.Syntax
        Poulet4.P4cub.BigStep.Value.IndPrincip
        Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Poulet4.P4cub.Syntax.Syntax.
Import Field.FieldTactics Val
       ValueNotations P.P4cubNotations.
Module TE := TypeEquivalence.

Section VE.
  (** Computational Value equality *)
  Fixpoint eqbv (v1 v2 : v) : bool :=
    let fix lstruct (vs1 vs2 : list v) : bool :=
        match vs1, vs2 with
        | [], [] => true
        | v1::vs1, v2::vs2 => eqbv v1 v2 && lstruct vs1 vs2
        | [], _::_ | _::_, [] => false
        end in
    let fix fields_struct (vs1 vs2 : Field.fs string v) : bool :=
        match vs1, vs2 with
        | [],           []           => true
        | (x1, v1)::vs1, (x2, v2)::vs2
          => equiv_dec x1 x2 &&&& eqbv v1 v2 && fields_struct vs1 vs2
        | [],            _::_
        | _::_,           []          => false
        end in
    let fix ffstruct (v1ss v2ss : list (bool * Field.fs string v)) : bool :=
        match v1ss, v2ss with
        | [], _::_ | _::_, [] => false
        | [], [] => true
        | (b1,vs1) :: v1ss, (b2, vs2) :: v2ss => (eqb b1 b2)%bool &&
                                              fields_struct vs1 vs2 &&
                                              ffstruct v1ss v2ss
        end in
    match v1, v2 with
    | VBool b1,       VBool b2       => eqb b1 b2
    | VInt w1 z1,     VInt w2 z2     => (w1 =? w2)%positive &&
                                       (z1 =? z2)%Z
    | VBit w1 n1,     VBit w2 n2     => (w1 =? w2)%N &&
                                       (n1 =? n2)%Z
    | VMatchKind mk1, VMatchKind mk2 => if equiv_dec mk1 mk2
                                       then true
                                       else false
    | VError err1,    VError err2    => if equiv_dec err1 err2
                                       then true
                                       else false
    | VTuple vs1, VTuple vs2         => lstruct vs1 vs2
    | VHeader vs1 b1, VHeader vs2 b2 => (eqb b1 b2)%bool && fields_struct vs1 vs2
    | VStruct vs1,    VStruct vs2    => fields_struct vs1 vs2
    | VHeaderStack ts1 vss1 n1 ni1,
      VHeaderStack ts2 vss2 n2 ni2   => F.eqb_fs TE.eqbt ts1 ts2 &&
                                       (n1 =? n2)%positive && (ni1 =? ni2)%Z &&
                                       ffstruct vss1 vss2
    | _,              _              => false
    end.
  (**[]*)
  
  Lemma eqbv_refl : forall vl : v, eqbv vl vl = true.
  Proof.
    Hint Rewrite eqb_reflx.
    Hint Rewrite Pos.eqb_refl.
    Hint Rewrite equiv_dec_refl.
    Hint Rewrite Z.eqb_refl.
    Hint Rewrite N.eqb_refl.
    Hint Rewrite TE.eqbt_refl.
    Hint Rewrite (@F.eqb_fs_reflx string E.t).
    Hint Rewrite andb_true_r.
    Hint Extern 0 => equiv_dec_refl_tactic : core.
    induction vl using custom_value_ind; simpl in *;
      autorewrite with core; simpl; auto;
        try match goal with
            | hs: list (bool * F.fs string v),
                  H: Forall _ ?hs
              |- _ => induction hs as [| [? ?] ? ?];
                      try inv_Forall_cons;
                      autorewrite with core;
                      unfold "∘" in *; simpl in *; intuition;
                        repeat (rewrite_true; simpl);
                        autorewrite with core;
                        match goal with
                        | H: Forall _ ?hs |- _ => clear H hs
                        end
            end;
        try ind_list_Forall; try ind_list_predfs;
          intuition; autorewrite with core; simpl;
            repeat (rewrite_true; simpl); auto.
  Qed.
  
  Import F.RelfEquiv.
  
  Ltac eq_true_terms :=
    match goal with
    | H: eqb _ _ = true |- _
      => apply eqb_prop in H; subst
    | H: (_ =? _)%positive = true |- _
      => apply Peqb_true_eq in H; subst
    | H: (_ =? _)%Z = true |- _
      => apply Z.eqb_eq in H; subst
    | H: context [equiv_dec ?x1 ?x2 &&&& _] |- _
      => destruct (equiv_dec x1 x2) as [? | ?];
        simpl in H; try discriminate
    | H: context [if equiv_dec ?t1 ?t2 then _ else _] |- _
      => destruct (equiv_dec t1 t2) as [? | ?];
        simpl in H; try discriminate
    | H: relop _ _ _ |- _ => inv H
    | H: F.eqb_fs TE.eqbt _ _ = true
      |- _ => pose proof eqb_fs_equiv _ _ TE.eqbt_reflect _ _ H as ?; clear H
    | H: F.relfs eq _ _ |- _ => apply eq_relfs in H; subst
    end.
  (**[]*)
  
  Ltac eauto_too_dumb :=
    match goal with
    | H: ?f ?x ?y = ?z,
         IH: (forall y, ?f ?x y = ?z -> _)
      |- _ => apply IH in H; clear IH
    end.
  
  Lemma eqbv_eq : forall v1 v2 : v, eqbv v1 v2 = true -> v1 = v2.
  Proof.
    induction v1 using custom_value_ind; intros []; intros;
      simpl in *; try discriminate;
        repeat destruct_andb;
        repeat (eq_true_terms); unfold equiv in *; auto; f_equal;
          repeat (eq_true_terms); auto;
            try match goal with
                | hs1: list (bool * F.fs string v),
                       IH: Forall _ ?hs1,
                           H: _ ?hs1 ?hs2 = true
                  |- ?hs1 = ?hs2
                  => generalize dependent hs2;
                      induction hs1 as [| [? ?] ? ?];
                      intros [| [? ?] ?]; intros; simpl in *;
                        try discriminate; auto; repeat destruct_andb;
                          inv_Forall_cons; repeat eq_true_terms;
                            unfold "∘" in *; simpl in *; intuition;
                              eauto_too_dumb; subst; repeat f_equal;
                                match goal with
                                | H: Forall _ ?l |- _ => clear H l
                                end
                end;
            try match goal with
                | IH: Forall _ ?vs1,
                      H: _ ?vs1 ?vs2 = true
                  |- ?vs1 = ?vs2
                  => generalize dependent vs2;
                      induction vs1; intros []; intros;
                        try discriminate; try inv_Forall_cons;
                          repeat destruct_andb; intuition;
                            repeat eauto_too_dumb; subst; auto
                end;
            try match goal with
                | IH: F.predfs_data _ ?fs1,
                      H: _ ?fs1 ?fs2 = true
                  |- ?fs1 = ?fs2
                  => generalize dependent fs2;
                      induction fs1; intros [| [? ?] ?]; intros;
                        try discriminate; try invert_cons_predfs;
                          try destruct_lifted_andb;
                          repeat destruct_andb; intuition;
                            unfold equiv in *; subst;
                              repeat eauto_too_dumb; subst; auto
                end.
    apply N.eqb_eq; assumption.
  Qed.
  
  Lemma eqbv_eq_iff : forall v1 v2 : v, eqbv v1 v2 = true <-> v1 = v2.
  Proof.
    Hint Resolve eqbv_refl : core.
    Hint Resolve eqbv_eq : core.
    intros; split; intros; subst; auto.
  Qed.
  
  Lemma eqbv_reflect : forall v1 v2, reflect (v1 = v2) (eqbv v1 v2).
  Proof.
    Hint Resolve eqbv_eq_iff : core.
    intros; reflect_split; auto; subst.
    rewrite eqbv_refl in Heqb; discriminate.
  Qed.
End VE.

Instance ValueEqDec : EqDec v eq :=
  { equiv_dec := fun v1 v2 => reflect_dec _ _ (eqbv_reflect v1 v2) }.
(**[]*)
