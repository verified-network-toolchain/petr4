Require Import Coq.Relations.Relations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Poulet4.P4automata.WP.
Import List.ListNotations.

Section BisimChecker.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Definition S: Type := S1 + S2.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.
  Context `{H_finite: @Finite H _ H_eq_dec}.

  Variable (a: P4A.t S H).

  Notation conf := (configuration (P4A.interp a)).

  Notation "⟦ x ⟧" := (interp_crel _ x).
  Notation "⦇ x ⦈" := (interp_conf_rel _ (a:=a) x).
  Notation "R ⊨ q1 q2" := (interp_crel _ R q1 q2) (at level 40).
  Notation "R ⊨ S" := (forall q1 q2, ⟦R⟧ q1 q2 -> ⦇S⦈ q1 q2) (at level 40).
  Notation δ := step.

  Reserved Notation "R ⇝ S" (at level 10).
  Inductive pre_bisimulation {c: bctx} : crel S H c -> crel S H c -> relation conf :=
  | PreBisimulationClose:
      forall R q1 q2,
        ⟦R⟧ q1 q2 ->
        R ⇝ [] q1 q2
  | PreBisimulationSkip:
      forall (R T: crel S H c) (C: conf_rel S H c) q1 q2,
        R ⊨ C ->
        R ⇝ T q1 q2 ->
        R ⇝ (C :: T) q1 q2
  | PreBisimulationExtend:
      forall (R T: crel S H c) (C: conf_rel S H c) q1 q2,
        (C :: R) ⇝ (T ++ WP.wp a C) q1 q2 ->
        R ⇝ (C :: T) q1 q2
  where "R ⇝ S" := (pre_bisimulation R S).

  Fixpoint range (n: nat) :=
    match n with
    | 0 => []
    | Datatypes.S n => range n ++ [n]
    end.

  Definition not_accept1 {c} (a: P4A.t S H) (s: S) : crel S H c := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true; st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl s;    st_buf_len := n |} |};
                   cr_rel := BRFalse _ _ |})
             (range (P4A.size a s)).

  Definition not_accept2 {c} (a: P4A.t S H) (s: S) : crel S H c := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl s;    st_buf_len := n |};
                               cs_st2 := {| st_state := inr true; st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ _ |})
             (range (P4A.size a s)).

  Definition init_rel {c} (a: P4A.t S H) : crel S H c := 
    List.concat (List.map (not_accept1 a) (enum S) ++
                 List.map (not_accept2 a) (enum S)).
  
End BisimChecker.
Arguments pre_bisimulation {_ _ _ _ _} {_ _} _ _ _.

Require Import Poulet4.P4automata.Examples.

Notation init_conf := (inl Simple.Start, [], []).
Notation "⟨ s1 , n1 ⟩ ⟨ s2 , n2 ⟩ ⊢ b" :=
  ({| cr_st :=
        {| cs_st1 := {| st_state := s1; st_buf_len := n1 |};
           cs_st2 := {| st_state := s2; st_buf_len := n2 |}; |};
      cr_rel := b|}) (at level 10).


Section SumInitRel.
  Set Implicit Arguments.
  Variables (S1 S2 H: Type).
  Context `{S1_fin: Finite S1}.
  Context `{S2_fin: Finite S2}.

  Definition sum_not_accept1 (a: P4A.t (S1 + S2) H) (s: S1) : crel (S1 + S2) H BCEmp := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl (inl s); st_buf_len := n |};
                               cs_st2 := {| st_state := inr true;    st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ _ |})
             (range (P4A.size a (inl s))).

  Definition sum_not_accept2 (a: P4A.t (S1 + S2) H) (s: S2) : crel (S1 + S2) H BCEmp := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true;    st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl (inr s); st_buf_len := n |} |};
                   cr_rel := BRFalse _ _ |})
             (range (P4A.size a (inr s))).

  Definition sum_init_rel (a: P4A.t (S1 + S2) H) : crel (S1 + S2) H BCEmp := 
    List.concat (List.map (sum_not_accept1 a) (enum S1) ++
                          List.map (sum_not_accept2 a) (enum S2)).
End SumInitRel.

Ltac pbskip :=
  apply PreBisimulationSkip;
  [intros;
   cbn in *;
   unfold interp_conf_rel, interp_store_rel, interp_conf_state in *;
   simpl in *;
   tauto|].


Ltac solve_bisim :=
  match goal with
  | |- pre_bisimulation _ _ _ [] _ _ => apply PreBisimulationClose
  | |- pre_bisimulation _ _ _ (_::_) _ _ => pbskip
  | |- pre_bisimulation _ _ _ (_::_) _ _ =>
    apply PreBisimulationExtend;
    unfold WP.wp, WP.wp_pred_pair, WP.st_pred, WP.wp_pred, WP.wp_op;
    simpl
  end.

From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
From Hammer Require Import Hammer.

Ltac pbskip' :=
  apply PreBisimulationSkip;
    [cbn in *;
     unfold interp_conf_rel,
            interp_store_rel,
            interp_conf_state,
            interp_state_template in *;
     sfirstorder;
     solve [hammer]|].

Ltac solve_bisim' :=
  match goal with
  | |- context[WP.wp _ _] =>
    progress (unfold WP.wp, WP.wp_pred_pair, WP.st_pred, WP.wp_pred, WP.wp_op; simpl)
  | |- pre_bisimulation _ _ _ _ _ _ _ _ [] _ _ => apply PreBisimulationClose
  | |- pre_bisimulation _ _ _ _ _ _ _ _ (_::_) _ _ => pbskip
  | |- pre_bisimulation _ _ _ _ _ _ _ _ (_::_) _ _ => apply PreBisimulationExtend; simpl
  | |- _ => progress simpl
  end.

Notation btrue := (BRTrue _ _).
Notation bfalse := (BRFalse _ _).
Notation "a ⇒ b" := (BRImpl a b) (at level 40).

Lemma prebisim_simple_split:
  pre_bisimulation _ _ _ _ _
                   SimpleSplit.aut
                   BCEmp
                   nil
                   (sum_init_rel SimpleSplit.aut)
                   (inl (inl Simple.Start), [], [])
                   (inl (inr Split.StSplit1), [], []).
Proof.
  unfold sum_init_rel.
  simpl.
  apply PreBisimulationExtend.
  simpl.
  time (repeat solve_bisim').
  cbv in *.
  intuition (try congruence).
Qed.

