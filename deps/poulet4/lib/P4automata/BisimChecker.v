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
  Variable (S_elems_replace_w_typeclass: list S).

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

  Definition not_accept1 (s: P4A.state_type a) : conf_rel a := 
    {| cr_st := {| cs_st1 := {| st_state := inr true; st_buf_len := 0 |};
                   cs_st2 := {| st_state := inl s;    st_buf_len := 0 |} |};
       cr_rel := BRFalse _ |}.

  Definition not_accept2 (s: P4A.state_type a) : conf_rel a := 
    {| cr_st := {| cs_st1 := {| st_state := inr true; st_buf_len := 0 |};
                   cs_st2 := {| st_state := inl s;    st_buf_len := 0 |} |};
       cr_rel := BRFalse _ |}.

  Definition init_rel : crel a := 
    List.map not_accept1 (P4A.list_states a) ++
    List.map not_accept2 (P4A.list_states a).
  
End BisimChecker.

Require Import Poulet4.P4automata.Examples.
Definition R0 := init_rel SimpleSplit.aut.

Lemma prebisim:
  forall q1 q2,
    pre_bisimulation (has_extract:=SimpleSplit.has_extract) R0 nil q1 q2.
Proof.
Abort.
       
