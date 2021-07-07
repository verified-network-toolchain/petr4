Require Import Coq.Relations.Relations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Poulet4.P4automata.WP.
Require Poulet4.P4automata.WPSymBit.
Require Poulet4.P4automata.WPSymLeap.
Require Poulet4.P4automata.Reachability.
Require Poulet4.P4automata.Bisimulations.
Import Bisimulations.SynPreSynWP.

Import List.ListNotations.


Locate "ctx , ⟨ s1 , n1 ⟩ ⟨ s2 , n2 ⟩ ⊢ b".
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
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.
  Context `{H_finite: @Finite H _ H_eq_dec}.

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
    List.nodup (@conf_rel_eq_dec _ _ _ _ _ _)
               (reachable_pairs_to_partition
                  (Reachability.reachable_states a n [s])).
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

Ltac pbskip_hammer :=
  apply PreBisimulationSkip;
    [intros [[s1 st1] buf1] [[s2 st2] buf2];
     repeat (unfold interp_crel,
             interp_conf_rel,
             interp_conf_state,
             interp_store_rel,
             interp_bit_expr,
             interp_store_rel,
             interp_state_template,
             RelationClasses.relation_conjunction,
             Relations.interp_rels
             || cbn);
     solve [sauto]|].

Ltac solve_bisim' :=
  match goal with
  | |- pre_bisimulation _ _ _ _ [] _ _ =>
    apply PreBisimulationClose
  | |- pre_bisimulation _ _ _ _ (_::_) _ _ =>
    pbskip_hammer
  | |- pre_bisimulation ?a ?wp _ _ (?C::_) _ _ =>
    let t := fresh "tmp" in
    pose (t := wp a C);
    apply PreBisimulationExtend with (W:=t); [reflexivity|];
    cbv in t;
    unfold t;
    clear t;
    simpl (_ ++ _)
  | |- _ => progress simpl
  end.

Ltac pbskip_plain :=
    apply PreBisimulationSkip;
     [ intros; cbn in *; unfold interp_conf_rel, interp_store_rel, interp_conf_state, interp_state_template in *;
        simpl in *;
      subst;
      intros;
      intuition;
      repeat 
        match goal with
        | [ X : P4automaton.configuration _ |- _ ] => destruct X as [[? ?] l]; destruct l
        | [ X : _ * _ |- _ ] => destruct X
        end;
        simpl in *; try solve [simpl in *; congruence]
        |].
  
Ltac solve_bisim_plain :=
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
    | |- pre_bisimulation _ _ _ _ [] _ _ =>
      apply PreBisimulationClose
    | |- pre_bisimulation _ _ _ _ (_::_) _ _ =>
      pbskip_plain; [idtac]
    | |- pre_bisimulation ?a ?wp _ _ (?C::_) _ _ =>
      let t := fresh "tmp" in
      pose (t := wp a C);
      apply PreBisimulationExtend with (W:=t); [reflexivity|];
      cbv in t;
      subst t
    | |- _ => progress simpl
    end.
