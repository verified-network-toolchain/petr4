Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Coq.micromega.Lia.
From Equations Require Import Equations.

Require Import Poulet4.Relations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Poulet4.P4automata.Syntax.
Module P4A := Poulet4.P4automata.Syntax.

Open Scope list_scope.

(* Bitstring variable context. *)
Inductive bctx :=
| BCEmp: bctx
| BCSnoc: bctx -> nat -> bctx.
Derive NoConfusion for bctx.
Derive EqDec for bctx.
Global Instance bctx_eq_dec : EquivDec.EqDec bctx eq := bctx_eqdec.

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
Derive NoConfusion for bvar.

Definition weaken_bvar {c} (size: nat) : bvar c -> bvar (BCSnoc c size) :=
  @BVarRest c size.

Equations bvar_eqdec {c} (x y: bvar c) : {x = y} + {x <> y} :=
  { bvar_eqdec (BVarTop _ _) (BVarTop _ _) := in_left;
    bvar_eqdec (BVarRest x') (BVarRest y') := if bvar_eqdec x' y'
                                              then in_left
                                              else in_right;
    bvar_eqdec _ _ := in_right }.
Next Obligation.
  dependent destruction H.
  eauto.
Qed.
#[global] Transparent bvar_eqdec.

Global Instance bvar_eq_dec {c}: EquivDec.EqDec (bvar c) eq := bvar_eqdec.

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

  Global Program Instance state_template_eq_dec : EquivDec.EqDec state_template eq :=
    { equiv_dec x y :=
        if x.(st_state) == y.(st_state)
        then if x.(st_buf_len) == y.(st_buf_len)
             then in_left
             else in_right
        else in_right }.
  Solve Obligations with (destruct x, y;
                           unfold equiv, complement in *;
                           simpl in *;
                           congruence).

  Definition interp_state_template (st: state_template) (c: conf) :=
    st.(st_state) = fst (fst c) /\
    List.length (snd c) = st.(st_buf_len).

  Inductive side := Left | Right.
  Derive NoConfusion for side.
  Derive EqDec for side.

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
  Derive NoConfusion for bit_expr.

  Definition beslice {c} (be: bit_expr c) (hi lo: nat) := 
    match be with 
    | BELit l => BELit (P4A.slice l hi lo)
    | BESlice x hi' lo' => BESlice x (hi' - hi) (lo' + lo)
    | _ => BESlice be hi lo
    end.

  Definition beconcat {c} (l: bit_expr c) (r: bit_expr c) := 
    match l, r with 
    | BELit l, BELit r => BELit (l ++ r)
    | _, _ => BEConcat l r
    end.
  

  Fixpoint weaken_bit_expr {c} (size: nat) (b: bit_expr c) : bit_expr (BCSnoc c size) :=
    match b with
    | BELit l => BELit l
    | BEBuf a => BEBuf a
    | BEHdr a h => BEHdr a h
    | BEVar b => BEVar (weaken_bvar size b)
    | BESlice e hi lo => BESlice (weaken_bit_expr size e) hi lo
    | BEConcat e1 e2 => BEConcat (weaken_bit_expr size e1) (weaken_bit_expr size e2)
    end.

  Obligation Tactic := intros.
  Unset Transparent Obligations.
  Equations bit_expr_eq_dec {c: bctx} : forall x y: bit_expr c, {x = y} + {x <> y} :=
    { bit_expr_eq_dec (BELit l) (BELit l') :=
        if l == l' then in_left else in_right;
      bit_expr_eq_dec (BEBuf a) (BEBuf a') :=
        if side_eqdec a a' then in_left else in_right;
      bit_expr_eq_dec (BEHdr a h) (BEHdr a' h') :=
        if Sumbool.sumbool_and _ _ _ _ (side_eqdec a a') (h == h')
        then in_left
        else in_right;
      bit_expr_eq_dec (BEVar x) (BEVar x') :=
        if bvar_eq_dec x x'
        then in_left
        else in_right;
      bit_expr_eq_dec (BESlice e hi lo) (BESlice e' hi' lo') :=
        if Sumbool.sumbool_and _ _ _ _ (hi == hi') (lo == lo')
        then if bit_expr_eq_dec e e'
             then in_left
             else in_right
        else in_right;
      bit_expr_eq_dec (BEConcat e1 e2) (BEConcat e1' e2') :=
        if bit_expr_eq_dec e1 e1'
        then if bit_expr_eq_dec e2 e2'
             then in_left
             else in_right
        else in_right;
             bit_expr_eq_dec _ _ := in_right }.

  Solve All Obligations with
      (intros;
      repeat match goal with
             | H: _ /\ _|- _ => destruct H
             | H: _ \/ _ |- _ => destruct H
             | |- ?g => congruence
             end).
  #[global] Transparent bit_expr_eq_dec.

  Global Program Instance bit_expr_eqdec {c} : EquivDec.EqDec (bit_expr c) eq :=
    { equiv_dec := bit_expr_eq_dec }.

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
      P4A.slice (interp_bit_expr e valu c1 c2) hi lo
    | BEConcat e1 e2 =>
      interp_bit_expr e1 valu c1 c2 ++ interp_bit_expr e2 valu c1 c2
    end.

  Lemma true_eq:
    forall x y : True,
      x = y.
  Proof using.
    destruct x, y; reflexivity.
  Qed.

  Inductive store_rel c :=
  | BRTrue
  | BRFalse
  | BREq (e1 e2: bit_expr c)
  | BRAnd (r1 r2: store_rel c)
  | BROr (r1 r2: store_rel c)
  | BRImpl (r1 r2: store_rel c).
  Arguments store_rel : default implicits.

  (* smart constructors *)

  Definition brand {c} (l: store_rel c) (r: store_rel c) :=  
    (* BRAnd l r. *)
    match l with 
    | BRTrue _ => r
    | BRFalse _ => BRFalse c
    | _ => 
      match r with 
      | BRTrue _ => l
      | BRFalse _ => BRFalse c
      | _ => BRAnd l r
      end
    end.

  Definition bror {c} (l: store_rel c) (r: store_rel c) := 
    (* BROr l r. *)
    match l with 
    | BRTrue _ => BRTrue c
    | BRFalse _ => r
    | _ => 
      match r with 
      | BRTrue _ => BRTrue c
      | BRFalse _ => l
      | _ => BROr l r
      end
    end.

  Definition brimpl {c} (l: store_rel c) (r: store_rel c) := 
    (* BRImpl l r. *)
      match l with 
      | BRTrue _ => r
      | BRFalse _ => BRTrue c
      | _ => 
        match r with 
        | BRTrue _ => BRTrue c
        | _ => BRImpl l r
        end
      end.
  

  Equations store_rel_eq_dec {c: bctx} : forall x y: store_rel c, {x = y} + {x <> y} :=
    { store_rel_eq_dec (BRTrue _) (BRTrue _) := in_left;
      store_rel_eq_dec (BRFalse _) (BRFalse _) := in_left;
      store_rel_eq_dec (BREq e11 e12) (BREq e21 e22) := 
        if Sumbool.sumbool_and _ _ _ _ (e11 == e21) (e12 == e22)
        then in_left
        else in_right;
      store_rel_eq_dec (BRAnd r11 r12) (BRAnd r21 r22) := 
        if (store_rel_eq_dec r11 r21)
        then if (store_rel_eq_dec r12 r22)
             then in_left
             else in_right
        else in_right;
      store_rel_eq_dec (BROr r11 r12) (BROr r21 r22) := 
        if (store_rel_eq_dec r11 r21)
        then if (store_rel_eq_dec r12 r22)
             then in_left
             else in_right
        else in_right;
      store_rel_eq_dec (BRImpl r11 r12) (BRImpl r21 r22) := 
        if (store_rel_eq_dec r11 r21)
        then if (store_rel_eq_dec r12 r22)
             then in_left
             else in_right
        else in_right;
    store_rel_eq_dec _ _ := in_right }.

  Solve All Obligations with
      (intros;
      repeat match goal with
             | H: _ /\ _|- _ => destruct H
             | H: _ \/ _ |- _ => destruct H
             | |- ?g => congruence
             end).
  #[global] Transparent store_rel_eq_dec.

  Global Program Instance store_rel_eqdec {c: bctx}: EquivDec.EqDec (store_rel c) eq :=
    store_rel_eq_dec.
  

  Fixpoint weaken_store_rel {c} (size: nat) (r: store_rel c) : store_rel (BCSnoc c size) :=
    match r with
    | BRTrue _ => BRTrue _
    | BRFalse _ => BRFalse _
    | BREq e1 e2 => BREq (weaken_bit_expr size e1) (weaken_bit_expr size e2)
    | BRAnd r1 r2 => brand (weaken_store_rel size r1) (weaken_store_rel size r2)
    | BROr r1 r2 => bror (weaken_store_rel size r1) (weaken_store_rel size r2)
    | BRImpl r1 r2 => BRImpl (weaken_store_rel size r1) (weaken_store_rel size r2)
    end.

  Fixpoint interp_store_rel {c} (r: store_rel c) (valu: bval c) (c1 c2: conf) : Prop :=
    match r with
    | BRTrue _ => True
    | BRFalse _ => False
    | BREq e1 e2 =>
      interp_bit_expr e1 valu c1 c2 = interp_bit_expr e2 valu c1 c2
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
  Global Program Instance conf_state_eq_dec: EquivDec.EqDec conf_state eq :=
    { equiv_dec x y :=
        if x.(cs_st1) == y.(cs_st1)
        then if x.(cs_st2) == y.(cs_st2) 
             then in_left
             else in_right
        else in_right }.
  Solve All Obligations with (destruct x, y; simpl in *; congruence).

  Record conf_rel :=
    { cr_st: conf_state;
      cr_ctx: bctx;
      cr_rel: store_rel cr_ctx }.
  Equations conf_rel_eq_dec: EquivDec.EqDec conf_rel eq :=
    { conf_rel_eq_dec x y with (bctx_eq_dec x.(cr_ctx) y.(cr_ctx)) :=
        { conf_rel_eq_dec ({| cr_st := st1;
                              cr_ctx := c;
                              cr_rel := rel1 |})
                          ({| cr_st := st2;
                              cr_ctx := c;
                              cr_rel := rel2 |})
                          (left eq_refl) :=
            if conf_state_eq_dec st1 st2
            then if store_rel_eq_dec rel1 rel2
                 then in_left
                 else in_right
            else in_right;
        conf_rel_eq_dec _ _ _ := in_right } }.
  Solve All Obligations with (try congruence).
  Next Obligation.
    intro Hs.
    inversion Hs.
    dependent destruction H2.
    eauto.
  Qed.
  #[global] Transparent conf_rel_eq_dec.

  Global Program Instance conf_rel_eqdec: EquivDec.EqDec conf_rel eq :=
    conf_rel_eq_dec.

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


  Notation "⊤" := rel_true.
  Notation "x ⊓ y" := (relation_conjunction x y) (at level 40).
  Notation "⟦ x ⟧" := (interp_conf_rel x).
  Definition interp_crel i (rel: crel) : relation conf :=
    interp_rels i (List.map interp_conf_rel rel).

End ConfRel.
Arguments interp_conf_rel {_} {_} {_} {_} {_} _.
Arguments interp_crel {_} {_} {_} {_} {_} _.
