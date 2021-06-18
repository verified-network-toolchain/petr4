Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
From Equations Require Import Equations.
Require Import Coq.Relations.Relations.

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

  Variable (a: P4A.t).
  Variable (has_extract: forall s H, 0 < P4A.size a (exist _ s H)).

  Notation conf := (configuration (P4A.interp a has_extract)).

  Inductive side := Left | Right.
  Inductive bit_expr :=
  | BELit (l: list bool)
  | BEBuf (a: side)
  | BEHdr (a: side) (h: P4A.hdr_ref)
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
    { cs_st1: state_template a;
      cs_st2: state_template a; }.

  Record conf_rel :=
    { cr_st: conf_state;
      cr_rel: store_rel; }.

  Definition interp_conf_state (c: conf_state) : relation conf :=
    fun c1 c2 =>
      interp_state_template _ has_extract c.(cs_st1) c1 /\
      interp_state_template _ has_extract c.(cs_st2) c2.
  
  Definition interp_conf_rel (c: conf_rel) : relation conf :=
    union _
      (interp_conf_state c.(cr_st))
      (interp_store_rel c.(cr_rel)).

  Definition chunked_relation :=
    list conf_rel.

  Definition rel_true: forall A, relation A :=
    fun _ x y => True.

  Fixpoint interp_chunked_relation (rel: chunked_relation) : relation conf :=
    match rel with
    | nil => rel_true _
    | r :: rel' => union _ (interp_conf_rel r) (interp_chunked_relation rel')
    end.

  (* Weakest preconditions *)
  Definition state_ref_eqb (x y: P4A.state_ref) : bool :=
    match x, y with
    | inr b, inr b' => Bool.eqb b b'
    | inl P4A.SNStart, inl P4A.SNStart => true
    | inl (P4A.SNName s), inl (P4A.SNName s') => String.eqb s s'
    | _, _ => false
    end.

  Definition expr_to_bit_expr (e: P4A.expr) (s: side) : bit_expr :=
    match e with
    | P4A.EHdr h => BEHdr s h
    | P4A.ELit bs => BELit bs
    end.

  Definition val_to_bit_expr (value: P4A.v) : bit_expr :=
    match value with
    | P4A.VBits bs => BELit bs
    end.

  Definition case_cond (cond: bit_expr) (st': P4A.state_ref) (s: P4A.sel_case) :=
    if state_ref_eqb st' (P4A.sc_st s)
    then BREq cond (val_to_bit_expr (P4A.sc_val s))
    else BRFalse.

  Definition cases_cond (cond: bit_expr) (st': P4A.state_ref) (s: list P4A.sel_case) :=
    List.fold_right BROr BRFalse (List.map (case_cond cond st') s).

  Fixpoint case_negated_conds (cond: bit_expr) (s: list P4A.sel_case) :=
    match s with
    | nil => BRTrue
    | s :: rest =>
      BRAnd
        (BRNotEq cond (val_to_bit_expr (P4A.sc_val s)))
        (case_negated_conds cond rest)
    end.

  Definition trans_cond (t: P4A.transition) (s: side) (st': P4A.state_ref) :=
    match t with
    | P4A.TGoto r =>
      if state_ref_eqb r st'
      then BRTrue
      else BRFalse
    | P4A.TSel cond cases default =>
      let be_cond := expr_to_bit_expr cond s in
      BROr (cases_cond be_cond st' cases)
           (if state_ref_eqb default st'
            then case_negated_conds be_cond cases
            else BRFalse)
    end.

End ConfRel.
