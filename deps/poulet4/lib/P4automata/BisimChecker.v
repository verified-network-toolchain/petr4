Require Import Coq.Relations.Relations.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Poulet4.P4automata.WP.
Import List.ListNotations.

Section BisimChecker.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.

  Variable (a: P4A.t S H).
  Variable (has_extract: forall s H, 0 < P4A.size (a:=a) (exist _ s H)).

  Notation conf := (configuration (P4A.interp a has_extract)).

  Notation "⟦ x ⟧" := (interp_crel x).
  Notation "⦇ x ⦈" := (interp_conf_rel (has_extract:=has_extract) x).
  Notation "R ⊨ q1 q2" := (interp_crel R q1 q2) (at level 40).
  Notation "R ⊨ S" := (forall q1 q2, ⟦R⟧ q1 q2 -> ⦇S⦈ q1 q2) (at level 40).
  Notation δ := step.

  Reserved Notation "R ⇝ S" (at level 10).
  Inductive pre_bisimulation : crel a -> crel a -> relation conf :=
  | PreBisimulationClose:
      forall R q1 q2,
        ⟦R⟧ q1 q2 ->
        R ⇝ [] q1 q2
  | PreBisimulationSkip:
      forall (R T: crel a) (C: conf_rel a) q1 q2,
        R ⇝ T q1 q2 ->
        R ⊨ C ->
        R ⇝ (C :: T) q1 q2
  | PreBisimulationExtend:
      forall (R T E: crel a) (C: conf_rel a) q1 q2,
        (C :: R) ⇝ (T ++ WP.wp C) q1 q2 ->
        R ⇝ (C :: T) q1 q2
  where "R ⇝ S" := (pre_bisimulation R S).
End BisimChecker.

Require Import Poulet4.P4automata.Examples.
