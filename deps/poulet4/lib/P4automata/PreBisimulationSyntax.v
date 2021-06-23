Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Coq.micromega.Lia.
From Equations Require Import Equations.
Require Import Coq.Relations.Relations.

Require Import Poulet4.P4automata.P4automaton.
Require Poulet4.P4automata.PreBisimulation.
Require Poulet4.P4automata.Syntax.
Module P4A := Poulet4.P4automata.Syntax.

Open Scope list_scope.

Section ConfRel.
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

  Record state_template :=
    { st_state: P4A.state_type a + bool;
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

  Inductive bit_expr :=
  | BELit (l: list bool)
  | BEBuf (a: side)
  | BEHdr (a: side) (h: P4A.hdr_ref H)
  | BESlice (e: bit_expr) (hi lo: nat)
  | BEConcat (e1 e2: bit_expr).

  Definition slice {A} (l: list A) (hi lo: nat) :=
    skipn lo (firstn (1 + hi) l).

  Fixpoint interp_bit_expr (e: bit_expr) (c1 c2: conf) : list bool :=
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
    | BESlice e hi lo =>
      slice (interp_bit_expr e c1 c2) hi lo
    | BEConcat e1 e2 =>
      interp_bit_expr e1 c1 c2 ++ interp_bit_expr e2 c1 c2
    end.

  Inductive store_rel :=
  | BRTrue
  | BRFalse
  | BREq (e1 e2: bit_expr)
  | BRNotEq (e1 e2: bit_expr)
  | BRAnd (r1 r2: store_rel)
  | BROr (r1 r2: store_rel).

  Fixpoint interp_store_rel (r: store_rel) (c1 c2: conf) : Prop :=
    match r with
    | BRTrue => True
    | BRFalse => False
    | BREq e1 e2 =>
      interp_bit_expr e1 c1 c2 = interp_bit_expr e2 c1 c2
    | BRNotEq e1 e2 =>
      interp_bit_expr e1 c1 c2 <> interp_bit_expr e2 c1 c2
    | BRAnd r1 r2 =>
      interp_store_rel r1 c1 c2 /\ interp_store_rel r2 c1 c2
    | BROr r1 r2 =>
      interp_store_rel r1 c1 c2 \/ interp_store_rel r2 c1 c2
    end.

  Record conf_state :=
    { cs_st1: state_template;
      cs_st2: state_template; }.

  Record conf_rel :=
    { cr_st: conf_state;
      cr_rel: store_rel; }.

  Definition interp_conf_state (c: conf_state) : relation conf :=
    fun c1 c2 =>
      interp_state_template c.(cs_st1) c1 /\
      interp_state_template c.(cs_st2) c2.
  
  Definition interp_conf_rel (c: conf_rel) : relation conf :=
    fun x y => 
      interp_conf_state c.(cr_st) x y ->
      interp_store_rel c.(cr_rel) x y.

  Definition chunked_relation :=
    list conf_rel.

  Definition rel_true: forall A, relation A :=
    fun _ x y => True.

  Fixpoint interp_chunked_relation (rel: chunked_relation) : relation conf :=
    match rel with
    | nil => @rel_true conf
    | r :: rel' => relation_conjunction (interp_conf_rel r) (interp_chunked_relation rel')
    end.

End ConfRel.
