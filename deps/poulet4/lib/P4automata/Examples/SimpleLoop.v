Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.PreBisimulationSyntax.

Require Import Poulet4.P4automata.Examples.ProofHeader.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module Loop.
  Inductive state :=
  | Start.
  Global Instance state_eqdec: EquivDec.EqDec state eq.
    vm_compute.
    intros.
    left.
    destruct x; destruct x0; trivial.
  Defined.
  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [Start] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header :=
  | Var.

  Global Instance hdr_eqdec: EquivDec.EqDec header eq.
    vm_compute.
    intros.
    left.
    destruct x; destruct x0; trivial.
  Defined.
  Global Program Instance header_finite: @Finite header _ hdr_eqdec :=
    {| enum := [Var] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := OpExtract 1 (HRVar Var);
         st_trans := P4A.TSel (CExpr (EHdr (HRVar Var)))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inl Start |};
                              {| sc_pat := PExact (VBits [false]);
                                 sc_st := inr true |}]
                              (inr false) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End Loop.

(* Lemma prebisim_loop:
  pre_bisimulation (Sum.sum Loop.aut Loop.aut)
                   (WPSymLeap.wp (H:=_))
                   nil
                   (mk_init 10 (Sum.sum Loop.aut Loop.aut) Loop.Start Loop.Start)
                   (inl (inl Loop.Start), [], [])
                   (inl (inr Loop.Start), [], []).
Proof.
  set (rel0 := mk_init 10 (Sum.sum Loop.aut Loop.aut) Loop.Start Loop.Start).
  cbv in rel0.
  subst rel0.
  solve_bisim'.
  solve_bisim'.
  Notation "x == y" := (BREq x y) (at level 40).
  Notation "side . x" := (BEHdr _ side x) (at level 40).
  Notation "⟪ x ⟫" := (HRVar x) (at level 40).
  Notation "⦃ x ⦄" := (BELit _ _ x) (at level 30).
  Notation "x ∨ y" := (BROr x y) (at level 30).
  simpl.
  solve_bisim'.
  solve_bisim'.
  solve_bisim'.
  solve_bisim'.
  solve_bisim'.
  solve_bisim'.
  apply PreBisimulationSkip;
   [ intros; cbn in *; unfold interp_conf_rel, interp_store_rel, interp_conf_state, interp_state_template in *;
      simpl in * |].
  {
    simpl.
    subst.
    intros.
    destruct valu as [[_ [b1 ?]] [b2 ?]].
    intuition.
    destruct q1 as [[? ?] ?], q2 as [[? ?] ?]; simpl in *.
    destruct l, l0; simpl in *; try solve [simpl in *; congruence].
  }
  apply PreBisimulationSkip;
   [ intros; cbn in *; unfold interp_conf_rel, interp_store_rel, interp_conf_state, interp_state_template in *;
      simpl in * |].
  {
    simpl.
    subst.
    intros.
    destruct valu as [[_ [b1 ?]] [b2 ?]].
    intuition.
    destruct q1 as [[? ?] ?], q2 as [[? ?] ?]; simpl in *.
    destruct l, l0; simpl in *; try solve [simpl in *; congruence].
  }
  solve_bisim'.
  cbv in *.
  intuition (try congruence).
Time Qed. *)

Module LoopUnroll.
  Inductive state :=
  | Start
  | Second.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [Start; Second] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header :=
  | Var.

  Global Instance hdr_eqdec: EquivDec.EqDec header eq.
    vm_compute.
    intros.
    left.
    destruct x; destruct x0; trivial.
  Defined.
  Global Program Instance header_finite: @Finite header _ hdr_eqdec :=
    {| enum := [Var] |}.
  Next Obligation.
    repeat constructor;
      repeat match goal with
             | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
             | |- ~ List.In _ [] => apply List.in_nil
             | |- ~ List.In _ (_ :: _) => unfold not; intros
             | H: List.In _ (_::_) |- _ => inversion H; clear H
             | _ => discriminate
             end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := OpExtract 1 (HRVar Var);
         st_trans := P4A.TSel (CExpr (EHdr (HRVar Var)))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inl Second |};
                              {| sc_pat := PExact (VBits [false]);
                                 sc_st := inr true |}]
                              (inr false) |}
    | Second =>
      {| st_op := OpExtract 1 (HRVar Var);
        st_trans := P4A.TSel (CExpr (EHdr (HRVar Var)))
                            [{| sc_pat := PExact (VBits [true]);
                                sc_st := inl Start |};
                            {| sc_pat := PExact (VBits [false]);
                                sc_st := inr true |}]
                            (inr false) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End LoopUnroll.

Definition comb_aut := Sum.sum Loop.aut LoopUnroll.aut.

Lemma prebisim_loop:
  pre_bisimulation (Sum.sum Loop.aut Loop.aut)
                   (WPSymLeap.wp (H:=_))
                   nil
                   (mk_init 10 (Sum.sum Loop.aut Loop.aut) Loop.Start Loop.Start)
                   (inl (inl Loop.Start), [], [])
                   (inl (inr Loop.Start), [], []).
Proof.
  set (rel0 := mk_init 10 (Sum.sum Loop.aut Loop.aut) Loop.Start Loop.Start).
  cbv in rel0.
  subst rel0.
  time (repeat (time solve_bisim')).
  cbv in *.
  intuition (try congruence).
Time Qed.

(* Ltac solve_bisim' :=
  match goal with
  | |- pre_bisimulation _ _ _ [] _ _ =>
    idtac "close";
    time apply PreBisimulationClose
  | |- pre_bisimulation _ _ _ (_ :: _) _ _ =>
    idtac "skip";
    time pbskip'
  | |- pre_bisimulation ?a ?wp ?R (?C :: ?T) ?a1 ?a2 =>
    idtac "extend";
    let t := fresh "tmp" in
    let Heqwp := fresh "Heqwp" in
    let Hext := fresh "Hext" in
    time pose (t := wp a C);
      time assert (Heqwp: t = wp a C) by reflexivity;
      time cbv in t;
      time pose proof (Hext := fun R' T' pf => PreBisimulationExtend _ _ _ comb_aut (WPSymLeap.wp (H:=Sum.H Loop.header LoopUnroll.header)) R' T' C t a1 a2 Heqwp pf);
      time unfold t in Hext;
      time apply (Hext R T);
      time clear Hext t Heqwp;
      time simpl (_ ++ _) 
  end. *)
(* 
Lemma prebisim_loop_unroll:
  pre_bisimulation comb_aut
                   (WPSymLeap.wp (H:=_))
                   nil
                   (mk_init 10 comb_aut Loop.Start LoopUnroll.Start)
                   (inl (inl Loop.Start), [], [])
                   (inl (inr LoopUnroll.Start), [], []).
Proof.
  set (rel0 := mk_init 10 comb_aut Loop.Start LoopUnroll.Start).
  cbv in rel0.
  subst rel0.
  do 10 solve_bisim'.
  do 10 solve_bisim'.
  do 10 solve_bisim'.
  do 10 solve_bisim'.
  do 10 solve_bisim'.
  time (repeat (time solve_bisim')).
  cbv in *.
  intuition (try congruence).
Time Qed.  *)