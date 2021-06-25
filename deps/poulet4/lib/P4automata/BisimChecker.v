Require Import Coq.Relations.Relations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Poulet4.P4automata.WP.
Import List.ListNotations.

Section BisimChecker.

  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.

  Variable (a: P4A.t S H).

  Notation conf := (configuration (P4A.interp a)).

  Notation "⟦ x ⟧" := (interp_crel a x).
  Notation "⦇ x ⦈" := (interp_conf_rel a x).
  Notation "R ⊨ q1 q2" := (interp_crel R q1 q2) (at level 40).
  Notation "R ⊨ S" := (forall q1 q2, ⟦R⟧ q1 q2 -> ⦇S⦈ q1 q2) (at level 40).
  Notation δ := step.

  Reserved Notation "R ⇝ S" (at level 10).
  Inductive pre_bisimulation : crel S H -> crel S H -> relation conf :=
  | PreBisimulationClose:
      forall R q1 q2,
        ⟦R⟧ q1 q2 ->
        R ⇝ [] q1 q2
  | PreBisimulationSkip:
      forall (R T: crel S H) (C: conf_rel S H) q1 q2,
        R ⊨ C ->
        R ⇝ T q1 q2 ->
        R ⇝ (C :: T) q1 q2
  | PreBisimulationExtend:
      forall (R T: crel S H) (C: conf_rel S H) q1 q2,
        (C :: R) ⇝ (T ++ WP.wp a C) q1 q2 ->
        R ⇝ (C :: T) q1 q2
  where "R ⇝ S" := (pre_bisimulation R S).

  Definition not_accept1 (s: S) : crel S H := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true; st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl s;    st_buf_len := n |} |};
                   cr_rel := BRFalse _ |})
             [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15].

  Definition not_accept2 (s: S) : crel S H :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl s;    st_buf_len := n |};
                               cs_st2 := {| st_state := inr true; st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ |})
             [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15].
              
  Definition init_rel : crel S H := 
    List.concat (List.map not_accept1 (enum S) ++
                 List.map not_accept2 (enum S)).
  
End BisimChecker.
Arguments pre_bisimulation {_ _ _ _ _} {_ _} _ _ _.

Require Import Poulet4.P4automata.Examples.

Notation S := (Sum.S Simple.state Split.state).
Notation H := (Sum.H Simple.header Split.header).
Notation init_conf := (inl Simple.Start, [], []).
Notation "⟨ s1 , n1 ⟩ ⟨ s2 , n2 ⟩ ⊢ b" :=
  ({| cr_st :=
        {| cs_st1 := {| st_state := s1; st_buf_len := n1 |};
           cs_st2 := {| st_state := s2; st_buf_len := n2 |}; |};
      cr_rel := b|}) (at level 10).

Ltac pbskip :=
  apply PreBisimulationSkip;
  [intros;
   cbn in *;
   unfold interp_conf_rel, interp_store_rel, interp_conf_state in *;
   simpl in *;
   tauto|].


Ltac solve_bisim :=
  match goal with
  | |- pre_bisimulation _ _ [] _ _ => apply PreBisimulationClose
  | |- pre_bisimulation _ _ (_::_) _ _ => pbskip
  | |- pre_bisimulation _ _ (_::_) _ _ =>
    apply PreBisimulationExtend;
    unfold WP.wp, WP.wp_pred_pair, WP.wp_edges, WP.wp_edge, WP.wp_op;
    simpl
  end.

Lemma prebisim:
  pre_bisimulation Simple.aut nil (init_rel _ _) init_conf init_conf.
Proof.
  apply PreBisimulationExtend.
  simpl.
  unfold WP.wp, WP.wp_pred_pair, WP.wp_edges, WP.wp_edge, WP.wp_op.
  simpl.
  repeat solve_bisim.
  cbv in *.
  intuition discriminate.
Qed.

From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
From Hammer Require Import Hammer.

Ltac pbskip' := apply PreBisimulationSkip; [hammer|].

Ltac solve_bisim' :=
  match goal with
  | |- context[WP.wp] => 
    unfold WP.wp, WP.wp_pred_pair, WP.wp_edges, WP.wp_edge, WP.wp_op;
    simpl
  | |- pre_bisimulation _ _ [] _ _ => apply PreBisimulationClose
  | |- pre_bisimulation _ _ (_::_) _ _ => pbskip
  | |- pre_bisimulation _ _ (_::_) _ _ =>
    apply PreBisimulationExtend;
    unfold WP.wp, WP.wp_pred_pair, WP.wp_edges, WP.wp_edge, WP.wp_op;
    simpl
  | |- _ => simpl
  end.


Lemma prebisim':
  pre_bisimulation Simple.aut nil (init_rel _ _) init_conf init_conf.
Proof.
  apply PreBisimulationExtend.
  repeat solve_bisim'.
  cbv in *.
  hammer.
Qed.
