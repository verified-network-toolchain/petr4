Require Import Coq.Relations.Relations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Poulet4.P4automata.WP.
Require Poulet4.P4automata.WPSymBit.
Require Poulet4.P4automata.WPSymLeap.
Require Poulet4.P4automata.Reachability.

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

  Variable (wp: P4A.t S H ->
                conf_rel S H ->
                list (conf_rel S H)).

  Notation conf := (configuration (P4A.interp a)).

  Notation "⟦ x ⟧" := (interp_crel x).
  Notation "⦇ x ⦈" := (interp_conf_rel (a:=a) x).
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
        (C :: R) ⇝ (T ++ wp a C) q1 q2 ->
        R ⇝ (C :: T) q1 q2
  where "R ⇝ S" := (pre_bisimulation R S).

  Fixpoint range (n: nat) :=
    match n with
    | 0 => []
    | Datatypes.S n => range n ++ [n]
    end.

  Definition not_accept1 (a: P4A.t S H) (s: S) : crel S H := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true; st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl s;    st_buf_len := n |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a s)).

  Definition not_accept2 (a: P4A.t S H) (s: S) : crel S H := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl s;    st_buf_len := n |};
                               cs_st2 := {| st_state := inr true; st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a s)).

  Definition init_rel (a: P4A.t S H) : crel S H := 
    List.concat (List.map (not_accept1 a) (enum S) ++
                 List.map (not_accept2 a) (enum S)).
  
End BisimChecker.
Arguments pre_bisimulation {S1 S2 H equiv2 H_eq_dec} a wp.

Require Import Poulet4.P4automata.Examples.

Notation init_conf := (inl Simple.Start, [], []).

Notation "ctx , ⟨ s1 , n1 ⟩ ⟨ s2 , n2 ⟩ ⊢ b" :=
  ({| cr_st :=
        {| cs_st1 := {| st_state := s1; st_buf_len := n1 |};
           cs_st2 := {| st_state := s2; st_buf_len := n2 |}; |};
      cr_ctx := ctx;
      cr_rel := b|}) (at level 10).
Notation btrue := (BRTrue _ _).
Notation bfalse := (BRFalse _ _).
Notation "a ⇒ b" := (BRImpl a b) (at level 40).

Section InitRels.
  Set Implicit Arguments.
  Variables (S1 S2 H: Type).
  Context `{S1_fin: Finite S1}.
  Context `{S2_fin: Finite S2}.

  Definition sum_not_accept1 (a: P4A.t (S1 + S2) H) (s: S1) : crel (S1 + S2) H := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl (inl s); st_buf_len := n |};
                               cs_st2 := {| st_state := inr true;    st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a (inl s))).

  Definition sum_not_accept2 (a: P4A.t (S1 + S2) H) (s: S2) : crel (S1 + S2) H := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true;    st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl (inr s); st_buf_len := n |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a (inr s))).

  Definition sum_init_rel (a: P4A.t (S1 + S2) H) : crel (S1 + S2) H := 
    List.concat (List.map (sum_not_accept1 a) (enum S1)
                          ++ List.map (sum_not_accept2 a) (enum S2)).

  Definition reachable_pair_to_partition '((s1, s2): Reachability.state_pair _ _)
    : crel (S1 + S2) H :=
    match s1.(st_state) with
    | inl st =>
      [BCEmp, ⟨inl st, s1.(st_buf_len)⟩ ⟨inr true, 0⟩ ⊢ bfalse]
    | inr st =>
      []
    end
      ++
      match s2.(st_state) with
      | inl st =>
        [BCEmp, ⟨inr true, 0⟩ ⟨inl st, s2.(st_buf_len)⟩ ⊢ bfalse]
      | inr st =>
        []
      end.

  Definition reachable_pairs_to_partition (r: Reachability.state_pairs _ _)
    : crel (S1 + S2) H :=
    List.concat (List.map reachable_pair_to_partition r).

  Definition mk_init (n: nat) (a: P4A.t (S1 + S2) H) s1 s2 :=
    let s := ({| st_state := inl (inl s1); st_buf_len := 0 |}, 
              {| st_state := inl (inr s2); st_buf_len := 0 |}) in
    reachable_pairs_to_partition
      (Reachability.reachable_states a 1000 [s]).
End InitRels.

Ltac pbskip :=
  apply PreBisimulationSkip;
  [intros;
   cbn in *;
   unfold interp_conf_rel, interp_store_rel, interp_conf_state in *;
   simpl in *;
   tauto|].


Ltac solve_bisim :=
  match goal with
  | |- pre_bisimulation _ WP.wp _ [] _ _ => apply PreBisimulationClose
  | |- pre_bisimulation _ WP.wp _ (_::_) _ _ => pbskip
  | |- pre_bisimulation _ WP.wp _ (_::_) _ _ =>
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
     intros;
     unfold interp_conf_rel,
            interp_store_rel,
            interp_conf_state,
            interp_state_template in *;
     simpl in *;
     sfirstorder;
     solve [hammer]|].

Ltac solve_bisim' :=
  match goal with
  | |- context[WPSymLeap.wp _ _] =>
    progress (
        unfold WPSymLeap.wp at -1;
        autounfold with wp;
        unfold WP.wp_op;
        simpl)
  | |- context[WPSymBit.wp _ _] =>
    progress (
        unfold WPSymBit.wp at -1;
        unfold
                WP.preds, WP.wp_pred_pair, WP.st_pred, WP.wp_pred, WP.wp_op,
                WPSymBit.wp_pred_pair 
              ; simpl)
  | |- context[WP.wp _ _] =>
    progress (
        unfold WP.wp at -1;
        unfold
                WP.preds, WP.wp_pred_pair, WP.st_pred, WP.wp_pred, WP.wp_op
              ; simpl)
  | |- pre_bisimulation _ _ _ [] _ _ => apply PreBisimulationClose
  | |- pre_bisimulation _ _ _ (_::_) _ _ => pbskip'
  | |- pre_bisimulation _ _ _ (_::_) _ _ => apply PreBisimulationExtend; simpl
  | |- _ => progress simpl
  end.

(*
Lemma prebisim_simple_split:
  pre_bisimulation SimpleSplit.aut
                   (WP.wp (H:=SimpleSplit.header))
                   nil
                   (sum_init_rel SimpleSplit.aut)
                   (inl (inl Simple.Start), [], [])
                   (inl (inr Split.StSplit1), [], []).
Proof.
  unfold sum_init_rel.
  time (repeat solve_bisim').
  cbv in *.
  intuition (try congruence).
Qed.

Lemma prebisim_simple_split_sym:
  pre_bisimulation SimpleSplit.aut
                   (WPSymBit.wp (H:=SimpleSplit.header))
                   nil
                   (sum_init_rel SimpleSplit.aut)
                   (inl (inl Simple.Start), [], [])
                   (inl (inr Split.StSplit1), [], []).
Proof.
  unfold sum_init_rel.
  do 90 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do   5 solve_bisim'.
  do 40 solve_bisim'.
  do 40 solve_bisim'.
  do 40 solve_bisim'.
  do 40 solve_bisim'.
  do 40 solve_bisim'.
  do 40 solve_bisim'.
  do 40 solve_bisim'.
  do 40 solve_bisim'.
  do 40 solve_bisim'.
  do 40 solve_bisim'.
  do 40 solve_bisim'.
  do 32 solve_bisim'.
  do 32 solve_bisim'.
  do 32 solve_bisim'.
  do 32 solve_bisim'.
  do 32 solve_bisim'.
  time (repeat (time solve_bisim')).
  cbv in *.
  intuition (try congruence).
Qed.

Lemma prebisim_simple_split_sym_leap:
  pre_bisimulation SimpleSplit.aut
                   (WPSymLeap.wp (H:=SimpleSplit.header))
                   nil
                   (sum_init_rel SimpleSplit.aut)
                   (inl (inl Simple.Start), [], [])
                   (inl (inr Split.StSplit1), [], []).
Proof.
  unfold sum_init_rel.
  do 200 solve_bisim'.
  cbv in *.
  intuition (try congruence).
Qed.
*)

Definition possibly_unsound_init_rel
  : crel (Simple.state + Split.state) (Sum.H Simple.header Split.header)
  :=
    [BCEmp, ⟨inl (inl Simple.Start), 0⟩ ⟨inr true, 0⟩ ⊢ bfalse;
    BCEmp, ⟨inl (inl Simple.Start), 4⟩ ⟨inr true, 0⟩ ⊢ bfalse;
    BCEmp, ⟨inr true, 0⟩ ⟨inl (inr Split.StSplit1), 0⟩ ⊢ bfalse;
    BCEmp, ⟨inr true, 0⟩ ⟨inl (inr Split.StSplit2), 0⟩ ⊢ bfalse].


Definition possibly_unsound_init_rel'
  : crel (Simple.state + Split.state) (Sum.H Simple.header Split.header)
  :=
    Eval compute in (mk_init 10 SimpleSplit.aut Simple.Start Split.StSplit1). 

(*
Lemma prebisim_simple_split_small_init:
  pre_bisimulation SimpleSplit.aut
                   (WP.wp (H:=SimpleSplit.header))
                   nil
                   (sum_init_rel SimpleSplit.aut)
                   (inl (inl Simple.Start), [], [])
                   (inl (inr Split.StSplit1), [], []).
Proof.
  unfold sum_init_rel.
  time (repeat solve_bisim').
  cbv in *.
  intuition (try congruence).
Qed.
*)

Lemma prebisim_simple_split_sym_small_init:
  pre_bisimulation SimpleSplit.aut
                   (WPSymBit.wp (H:=SimpleSplit.header))
                   nil
                   possibly_unsound_init_rel'
                   (inl (inl Simple.Start), [], [])
                   (inl (inr Split.StSplit1), [], []).
Proof.
  unfold possibly_unsound_init_rel'.
  time (repeat solve_bisim').
  cbv in *.
  intuition (try congruence).
Qed.

Lemma prebisim_simple_split_sym_leap_small_init:
  pre_bisimulation SimpleSplit.aut
                   (WPSymLeap.wp (H:=SimpleSplit.header))
                   nil
                   possibly_unsound_init_rel'
                   (inl (inl Simple.Start), [], [])
                   (inl (inr Split.StSplit1), [], []).
Proof.
  unfold possibly_unsound_init_rel'.
  time (repeat solve_bisim').
  cbv in *.
  intuition (try congruence).
Qed.
