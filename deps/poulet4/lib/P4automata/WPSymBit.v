Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.FinType.
Require Poulet4.P4automata.Syntax.
Module P4A := Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Poulet4.P4automata.WP.
Import ListNotations.

Section WeakestPreSymbolicBit.
  Set Implicit Arguments.
  
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

  Definition wp_pred_pair
             (phi: conf_rel S H)
             (preds: WP.pred S1 S2 H phi.(cr_ctx) * WP.pred _ _ _ phi.(cr_ctx))
    : list (conf_rel S H) :=
    let '(sl, sr) := preds in
    let size := 1 in
    let sl := WP.weaken_pred size sl in
    let sr := WP.weaken_pred size sr in
    let phi_rel := weaken_store_rel size phi.(cr_rel) in
    let b := (BEVar H (BVarTop phi.(cr_ctx) size)) in
    [{| cr_st := {| cs_st1 := WP.st_pred a sl;
                    cs_st2 := WP.st_pred a sr |};
        cr_rel := WP.wp_pred a Left b sl (WP.wp_pred a Right b sr phi_rel) |}].
     
  Definition wp (phi: conf_rel S H) : list (conf_rel S H) :=
    let cur_st_left  := phi.(cr_st).(cs_st1) in
    let cur_st_right := phi.(cr_st).(cs_st2) in
    let pred_pairs := list_prod (WP.preds a Left ([inr false; inr true] ++ List.map (fun s => inl (inl s)) (enum S1)) cur_st_left)
                                (WP.preds a Right ([inr false; inr true] ++ List.map (fun s => inl (inr s)) (enum S2)) cur_st_right) in
    List.concat (List.map (wp_pred_pair phi) pred_pairs).

End WeakestPreSymbolicBit.
