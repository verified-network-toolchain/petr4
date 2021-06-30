Require Import Coq.Classes.EquivDec.
Require Import Coq.Relations.Relations.
Require Import Coq.Program.Program.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Poulet4.P4automata.WP.
Require Poulet4.P4automata.WPSymBit.
Require Poulet4.P4automata.WPSymLeap.

Import List.ListNotations.

Set Implicit Arguments.
Section ReachablePairs.

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

  Definition state_pair : Type :=
    state_template S * state_template S.
  Global Program Instance state_pair_eq_dec: EquivDec.EqDec state_pair eq :=
    { equiv_dec x y :=
        if Sumbool.sumbool_and _ _ _ _
             (state_template_eq_dec (fst x) (fst y))
             (state_template_eq_dec (snd x) (snd y))
        then in_left
        else in_right }.
  Next Obligation.
    destruct x, y.
    simpl in *.
    congruence.
  Qed.
  Next Obligation.
    intuition.
  Qed.

  Definition state_pairs : Type :=
    list state_pair.

  Definition possible_next_states (st: P4A.state S H) : list (P4A.state_ref S) :=
    match st.(P4A.st_trans) with
    | P4A.TGoto _ s' =>
      [s']
    | P4A.TSel _ cases default =>
      default :: List.map (fun c => P4A.sc_st c) cases
    end.

  Definition reads_left (s: S) (buf_len: nat) :=
    P4A.size a s - buf_len.

  Definition advance (steps: nat) (t1: state_template S) (st: P4A.state S H) :=
    if t1.(st_buf_len) + steps == P4A.state_size st
    then List.map (fun r => {| st_state := r; st_buf_len := 0 |}) (possible_next_states st)
    else [{| st_state := t1.(st_state); st_buf_len := t1.(st_buf_len) + steps |}].

  Definition reachable_pair_step (r0: state_pair) : state_pairs :=
    let '(t1, t2) := r0 in
    match t1.(st_state), t2.(st_state) with
    | inl s1, inl s2 => 
      let st1 := P4A.t_states a s1 in
      let st2 := P4A.t_states a s2 in
      let len1 := t1.(st_buf_len) in
      let len2 := t2.(st_buf_len) in
      let steps := Nat.min (reads_left s1 len1)
                           (reads_left s2 len2) in
      List.list_prod (advance steps t1 st1)
                     (advance steps t2 st2)
    | _, _ => [] (* is this right? *)
    end.
  
  Definition reachable_step (r: state_pairs) : state_pairs :=
    let r' := (List.concat (List.map reachable_pair_step r)) in
    List.nodup state_pair_eq_dec (r' ++ r).

  Fixpoint reachable_states (fuel: nat) (r: state_pairs) :=
    match fuel with
    | 0 => r
    | Datatypes.S fuel => reachable_states fuel (reachable_step r)
    end.

End ReachablePairs.
