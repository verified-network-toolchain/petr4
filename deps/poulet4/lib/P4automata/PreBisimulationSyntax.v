Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
From Equations Require Import Equations.

Require Import Poulet4.P4automata.P4automaton.
Require Poulet4.P4automata.PreBisimulation.
Require Poulet4.P4automata.Syntax.
Module P4A := Poulet4.P4automata.Syntax.

Open Scope list_scope.

Section StateTemplate.
  Variable (a: P4A.t).
  Variable (has_extract: forall s H, 0 < P4A.size a (exist _ s H)).
  Notation conf := (configuration (P4A.interp a has_extract)).

  Record state_template :=
    { st_state: P4A.state_type a + bool;
      st_buf_len: nat }.

  Definition interp_state_template (st: state_template) (c: conf) :=
    st.(st_state) = fst (fst c) /\
    List.length (snd c) = st.(st_buf_len).

End StateTemplate.

Section ConfRel.

  Variable (a1 a2: P4A.t).
  Variable (has_extract1: forall s H, 0 < P4A.size a1 (exist _ s H)).
  Variable (has_extract2: forall s H, 0 < P4A.size a2 (exist _ s H)).

  Notation conf1 := (configuration (P4A.interp a1 has_extract1)).
  Notation conf2 := (configuration (P4A.interp a2 has_extract2)).

  Inductive bit_expr :=
  | BEBuf (automaton: bool)
  | BEHdr (automaton: bool) (h: P4A.hdr_ref)
  | BESlice (e: bit_expr) (hi lo: nat)
  | BEConcat (e1 e2: bit_expr).

  Definition slice {A} (l: list A) (hi lo: nat) :=
    skipn lo (firstn (1 + hi) l).

  Fixpoint interp_bit_expr (e: bit_expr) (c1: conf1) (c2: conf2) : list bool :=
    match e with
    | BEBuf automaton => if automaton then snd c1 else snd c2
    | BEHdr automaton h =>
      let store := if automaton then snd (fst c1) else snd (fst c2) in
      match P4A.find h store with
      | P4A.VBits v => v
      end
    | BESlice e hi lo =>
      slice (interp_bit_expr e c1 c2) hi lo
    | BEConcat e1 e2 =>
      interp_bit_expr e1 c1 c2 ++ interp_bit_expr e2 c1 c2
    end.

  Inductive store_rel :=
  | BREq (e1 e2: bit_expr)
  | BRNotEq (e1 e2: bit_expr)
  | BRAnd (r1 r2: store_rel).

  Fixpoint interp_store_rel (r: store_rel) (c1: conf1) (c2: conf2) : Prop :=
    match r with
    | BREq e1 e2 =>
      interp_bit_expr e1 c1 c2 = interp_bit_expr e2 c1 c2
    | BRNotEq e1 e2 =>
      interp_bit_expr e1 c1 c2 <> interp_bit_expr e2 c1 c2
    | BRAnd r1 r2 =>
      interp_store_rel r1 c1 c2 /\ interp_store_rel r2 c1 c2
    end.

  Record conf_rel :=
    { cr_st1: state_template a1;
      cr_st2: state_template a2;
      cr_rel: store_rel; }.

  Definition interp_conf_rel (c: conf_rel) (c1: conf1) (c2: conf2) :=
    interp_state_template _ has_extract1 c.(cr_st1) c1 /\
    interp_state_template _ has_extract2 c.(cr_st2) c2 /\
    interp_store_rel c.(cr_rel) c1 c2.

  Definition chunked_relation :=
    list conf_rel.

  Definition interp_chunked_relation (rel: chunked_relation) (c1: conf1) (c2: conf2) : Prop :=
    List.Forall (fun r => interp_conf_rel r c1 c2) rel.

End ConfRel.
