Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Coq.micromega.Lia.
From Equations Require Import Equations.
Require Import Coq.Relations.Relations.

Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Poulet4.P4automata.PreBisimulation.
Require Poulet4.P4automata.Syntax.
Module P4A := Poulet4.P4automata.Syntax.

Open Scope list_scope.

(* Bitstring variable context. *)
Inductive bctx :=
| BCEmp: bctx
| BCSnoc: bctx -> nat -> bctx.
Derive NoConfusion for bctx.

(* Bitstring variable valuation. *)
Fixpoint bval (c: bctx) : Type :=
  match c with
  | BCEmp => unit
  | BCSnoc c' size => bval c' * {b: list bool | List.length b = size}
  end.

Inductive bvar : bctx -> Type :=
| BVarTop:
    forall c size,
      bvar (BCSnoc c size)
| BVarRest:
    forall c size,
      bvar c ->
      bvar (BCSnoc c size).
Arguments BVarRest {_ _} _.

Definition weaken_bvar {c} (size: nat) : bvar c -> bvar (BCSnoc c size) :=
  @BVarRest c size.

Equations bvar_eqdec {c} (x y: bvar c) : {x = y} + {x <> y} :=
  { bvar_eqdec (BVarTop _ _) (BVarTop _ _) := in_left;
    bvar_eqdec (BVarRest x') (BVarRest y') := if bvar_eqdec x' y'
                                              then in_left
                                              else in_right;
    bvar_eqdec _ _ := in_right }.
Next Obligation. dependent destruction H. tauto. Qed.

Instance bvar_eq_dec {c}: EquivDec.EqDec (bvar c) eq := bvar_eqdec.

Fixpoint check_bvar {c} (x: bvar c) : nat :=
  match x with
  | BVarTop c size => size
  | BVarRest x' => check_bvar x'
  end.

Equations interp_bvar {c} (valu: bval c) (x: bvar c) : list bool :=
  { interp_bvar (_, bs)    (BVarTop _ _)  := proj1_sig bs;
    interp_bvar (valu', bs) (BVarRest x')  := interp_bvar valu' x' }.

Section ConfRel.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.
  Context `{H_finite: @Finite H _ H_eq_dec}.

  Variable (a: P4A.t S H).

  Notation conf := (configuration (P4A.interp a)).

  Record state_template :=
    { st_state: P4A.state_ref S;
      st_buf_len: nat }.

  Definition interp_state_template (st: state_template) (c: conf) :=
    st.(st_state) = fst (fst c) /\
    List.length (snd c) = st.(st_buf_len).

  Inductive side := Left | Right.
  Global Program Instance side_eq_dec : EquivDec.EqDec side eq :=
    { equiv_dec x y :=
        match x, y with
        | Left, Left => in_left
        | Right, Right => in_left
        | Left, Right => in_right
        | Right, Left => in_right
        end }.
  Solve Obligations with unfold equiv, complement in *; congruence.

  Inductive bit_expr (c: bctx) :=
  | BELit (l: list bool)
  | BEBuf (a: side)
  | BEHdr (a: side) (h: P4A.hdr_ref H)
  | BEVar (b: bvar c)
  | BESlice (e: bit_expr c) (hi lo: nat)
  | BEConcat (e1 e2: bit_expr c).
  Arguments BELit {c} _.
  Arguments BEBuf {c} _.
  Arguments BEHdr {c} _ _.

  Fixpoint weaken_bit_expr {c} (size: nat) (b: bit_expr c) : bit_expr (BCSnoc c size) :=
    match b with
    | BELit l => BELit l
    | BEBuf a => BEBuf a
    | BEHdr a h => BEHdr a h
    | BEVar b => BEVar (weaken_bvar size b)
    | BESlice e hi lo => BESlice (weaken_bit_expr size e) hi lo
    | BEConcat e1 e2 => BEConcat (weaken_bit_expr size e1) (weaken_bit_expr size e2)
    end.

  Fixpoint size {c} (be: bit_expr c) : nat :=
    match be with
    | BELit _
    | BEBuf _
    | BEHdr _ _
    | BEVar _ => 1
    | BESlice e _ _ => 1 + size e
    | BEConcat e1 e2 => 1 + size e1 + size e2
    end.

  Ltac solve_bit_expr_dec :=
    unfold not in *;
    intros;
    subst;
    try (firstorder congruence);
    (try match goal with
        | H: bit_expr |- _ =>
          destruct H
         end);
    (firstorder eauto);
    (firstorder congruence).

  Obligation Tactic := intros.
  Unset Transparent Obligations.
  Program Fixpoint bit_expr_eqdec {c} (x y: bit_expr c) {measure (size x)} : {x = y} + {x <> y} :=
    match x with
    | BELit l =>
      match y with
      | BELit l' => if l == l' then in_left else in_right
      | _ => in_right
      end
    | BEBuf a =>
      match y with
      | BEBuf a' => if a == a' then in_left else in_right
      | _ => in_right
      end
    | BEHdr a h =>
      match y with
      | BEHdr a' h' =>
        if Sumbool.sumbool_and _ _ _ _ (a == a') (h == h')
        then in_left
        else in_right
      | _ => in_right
      end
    | BEVar x =>
      match y with
      | BEVar x' =>
        if bvar_eq_dec x x'
        then in_left
        else in_right
      | _ => in_right
      end
    | BESlice e hi lo =>
      match y with
      | BESlice e' hi' lo' =>
        if Sumbool.sumbool_and _ _ _ _ (hi == hi') (lo == lo')
        then if bit_expr_eqdec e e'
             then in_left
             else in_right
        else in_right
      | _ => in_right
      end
    | BEConcat e1 e2 =>
      match y with
      | BEConcat e1' e2' =>
        if bit_expr_eqdec e1 e1'
        then if bit_expr_eqdec e2 e2'
             then in_left
             else in_right
        else in_right
      | _ => in_right
      end
    end.
  Solve All Obligations with solve_bit_expr_dec.
  Next Obligation. subst; simpl; Lia.lia. Qed.
  Next Obligation. subst; simpl; Lia.lia. Qed.
  Next Obligation. unfold wildcard' in *; solve_bit_expr_dec. Qed.
  Next Obligation. unfold wildcard' in *; solve_bit_expr_dec. Qed.
  Next Obligation. unfold wildcard' in *; solve_bit_expr_dec. Qed.
  Next Obligation. unfold wildcard' in *; solve_bit_expr_dec. Qed.
  Next Obligation. unfold wildcard' in *; solve_bit_expr_dec. Qed.
  Next Obligation.
    set (f := (fun recarg : {c : bctx & {_ : bit_expr c & bit_expr c}} =>
                 let c := projT1 recarg in
                 let x := projT1 (projT2 recarg) in let y := projT2 (projT2 recarg) in size x)).
    eapply (Wf_nat.well_founded_lt_compat _ f).
    intros [x x'] [y y'] Hmr.
    inversion Hmr; cbn in *; Lia.lia.
  Qed.

  Global Program Instance bit_expr_eq_dec {c} : EquivDec.EqDec (bit_expr c) eq :=
    { equiv_dec := bit_expr_eqdec }.

  Definition slice {A} (l: list A) (hi lo: nat) :=
    skipn lo (firstn (1 + hi) l).

  Fixpoint interp_bit_expr {c} (e: bit_expr c) (valu: bval c) (c1 c2: conf) : list bool :=
    match e with
    | BELit l => l
    | BEBuf Left => snd c1
    | BEBuf Right => snd c2
    | BEHdr a h =>
      let c := match a with
               | Left => c1
               | Right => c2
               end
      in
      match P4A.find h (snd (fst c)) with
      | P4A.VBits v => v
      end
    | BEVar x => interp_bvar valu x
    | BESlice e hi lo =>
      slice (interp_bit_expr e valu c1 c2) hi lo
    | BEConcat e1 e2 =>
      interp_bit_expr e1 valu c1 c2 ++ interp_bit_expr e2 valu c1 c2
    end.

  Inductive store_rel c :=
  | BRTrue
  | BRFalse
  | BREq (e1 e2: bit_expr c)
  | BRNotEq (e1 e2: bit_expr c)
  | BRAnd (r1 r2: store_rel c)
  | BROr (r1 r2: store_rel c)
  | BRImpl (r1 r2: store_rel c).
  Arguments store_rel : default implicits.

  Fixpoint weaken_store_rel {c} (size: nat) (r: store_rel c) : store_rel (BCSnoc c size) :=
    match r with
    | BRTrue _ => BRTrue _
    | BRFalse _ => BRFalse _
    | BREq e1 e2 => BREq (weaken_bit_expr size e1) (weaken_bit_expr size e2)
    | BRNotEq e1 e2 => BRNotEq (weaken_bit_expr size e1) (weaken_bit_expr size e2)
    | BRAnd r1 r2 => BRAnd (weaken_store_rel size r1) (weaken_store_rel size r2)
    | BROr r1 r2 => BROr (weaken_store_rel size r1) (weaken_store_rel size r2)
    | BRImpl r1 r2 => BRImpl (weaken_store_rel size r1) (weaken_store_rel size r2)
    end.

  Fixpoint interp_store_rel {c} (r: store_rel c) (valu: bval c) (c1 c2: conf) : Prop :=
    match r with
    | BRTrue _ => True
    | BRFalse _ => False
    | BREq e1 e2 =>
      interp_bit_expr e1 valu c1 c2 = interp_bit_expr e2 valu c1 c2
    | BRNotEq e1 e2 =>
      interp_bit_expr e1 valu c1 c2 <> interp_bit_expr e2 valu c1 c2
    | BRAnd r1 r2 =>
      interp_store_rel r1 valu c1 c2 /\ interp_store_rel r2 valu c1 c2
    | BROr r1 r2 =>
      interp_store_rel r1 valu c1 c2 \/ interp_store_rel r2 valu c1 c2
    | BRImpl r1 r2 =>
      interp_store_rel r1 valu c1 c2 -> interp_store_rel r2 valu c1 c2
    end.

  Record conf_state :=
    { cs_st1: state_template;
      cs_st2: state_template; }.

  Record conf_rel :=
    { cr_st: conf_state;
      cr_ctx: bctx;
      cr_rel: store_rel cr_ctx }.

  Definition interp_conf_state (c: conf_state) : relation conf :=
    fun c1 c2 =>
      interp_state_template c.(cs_st1) c1 /\
      interp_state_template c.(cs_st2) c2.
  
  Definition interp_conf_rel (phi: conf_rel) : relation conf :=
    fun x y => 
      interp_conf_state phi.(cr_st) x y ->
      forall valu,
        interp_store_rel phi.(cr_rel) valu x y.

  Definition crel :=
    list (conf_rel).

  Definition rel_true: forall {A}, relation A :=
    fun _ x y => True.

  Notation "⊤" := rel_true.
  Notation "x ⊓ y" := (relation_conjunction x y) (at level 40).
  Notation "⟦ x ⟧" := (interp_conf_rel x).
  Fixpoint interp_crel (rel: crel) : relation conf :=
    match rel with
    | [] => ⊤
    | r :: rel' => ⟦r⟧ ⊓ interp_crel rel'
    end.

End ConfRel.
Arguments interp_conf_rel {_} {_} {_} {_} {_} _.
Arguments interp_crel {_} {_} {_} {_} {_} _.
