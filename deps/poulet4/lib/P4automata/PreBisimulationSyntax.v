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
  | BEBuf (a: side)
  | BEHdr (a: side) (h: P4A.hdr_ref)
  | BESlice (e: bit_expr) (hi lo: nat)
  | BEConcat (e1 e2: bit_expr).

  Definition slice {A} (l: list A) (hi lo: nat) :=
    skipn lo (firstn (1 + hi) l).

  Fixpoint interp_bit_expr (e: bit_expr) (c1 c2: conf) : list bool :=
    match e with
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
  | BREq (e1 e2: bit_expr)
  | BRNotEq (e1 e2: bit_expr)
  | BRAnd (r1 r2: store_rel).

  Fixpoint interp_store_rel (r: store_rel) (c1 c2: conf) : Prop :=
    match r with
    | BREq e1 e2 =>
      interp_bit_expr e1 c1 c2 = interp_bit_expr e2 c1 c2
    | BRNotEq e1 e2 =>
      interp_bit_expr e1 c1 c2 <> interp_bit_expr e2 c1 c2
    | BRAnd r1 r2 =>
      interp_store_rel r1 c1 c2 /\ interp_store_rel r2 c1 c2
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

  Definition trans_states (t: P4A.transition) : list P4A.state_ref :=
    match t with
    | P4A.TGoto r => [r]
    | P4A.TSel _ cases default => default :: List.map P4A.sc_st cases
    end.

  Definition succs (a: P4A.t) (s: P4A.state_name) : list P4A.state_ref :=
    match Envn.Env.find s a with
    | Some s_init => trans_states s_init.(P4A.st_trans)
    | None => []
    end.

  Definition state_ref_eqb (x y: P4A.state_ref) : bool :=
    match x, y with
    | inr b, inr b' => Bool.eqb b b'
    | inl P4A.SNStart, inl P4A.SNStart => true
    | inl (P4A.SNName s), inl (P4A.SNName s') => String.eqb s s'
    | _, _ => false
    end.

  Definition may_succede (a: P4A.t) (s: P4A.state_name) (s': P4A.state_ref) :=
    List.existsb (fun s0 => state_ref_eqb s0 s') (succs a s).

  Definition list_states (a: P4A.t) : list P4A.state_name :=
    List.nodup Syntax.state_name_eq_dec (List.map fst a).

  Definition preds (a: P4A.t) (s': P4A.state_ref) :=
    List.filter (fun s => may_succede a s s') (list_states a).

End ConfRel.
