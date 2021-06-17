Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
From Equations Require Import Equations.

Require Import Poulet4.P4automata.P4automaton.
Require Poulet4.P4automata.PreBisimulation.
Require Poulet4.P4automata.Syntax.
Module P4A := Poulet4.P4automata.Syntax.

Open Scope list_scope.

Section StateCond.
  Variable (a: P4A.t).
  Variable (has_extract: forall s H, 0 < P4A.size a (exist _ s H)).

  Inductive bit_context :=
  | BCEmp
  | BCSnoc (bits: nat) (rest: bit_context) 
  .
  Derive NoConfusion for bit_context.

  Inductive bit_var: bit_context -> Type :=
  | BVHd: forall {bits rest}, bit_var (BCSnoc bits rest)
  | BVTl: forall {bits rest}, bit_var rest -> bit_var (BCSnoc bits rest)
  .

  Fixpoint shift_bit_var {bc: bit_context} {bits: nat} (bv: bit_var bc) : bit_var (BCSnoc bits bc) :=
    match bv with
    | BVHd => BVTl BVHd
    | BVTl bv' => BVTl (shift_bit_var bv')
    end.

  Inductive bit_valuation : bit_context -> Type :=
  | BVEmp: bit_valuation BCEmp
  | BVSnoc (val: list bool): forall bits rest,
      bit_valuation rest ->
      List.length val = bits ->
      bit_valuation (BCSnoc bits rest).

  Equations bit_valuation_lookup : forall bc: bit_context, bit_valuation bc -> bit_var bc -> list bool :=
    { bit_valuation_lookup _ (BVSnoc val _ _ _ _) BVHd := val;
      bit_valuation_lookup _ (BVSnoc val _ _ bv' _) (BVTl var') :=
        bit_valuation_lookup _ bv' var' }.

  Inductive bit_expr bc : Type :=
  | BESnoct (bits : list bool)
  | BEApp (vars: list (bit_var bc)).

  Definition interp_bit_expr {bc} (bv: bit_valuation bc) (b: bit_expr bc) (bits: list bool) :=
    match b with 
    | BESnoct _ bits' => bits = bits'
    | BEApp _ vars =>
      List.concat (List.map (fun var => bit_valuation_lookup _ bv var) vars) = bits
    end.

  Inductive store_constraint bc :=
  | SCEq (k: P4A.hdr_ref) (v: bit_expr bc)
  | SCNeq (k: P4A.hdr_ref) (v: list bool).

  Definition interp_store_constraint {bc} (bv: bit_valuation bc) (sc: store_constraint bc) (st: P4A.store) : Prop :=
    match sc with
    | SCEq _ k v =>
      match P4A.find k st with
      | P4A.VBits bits => interp_bit_expr bv v bits
      end
    | SCNeq _ k v =>
      match P4A.find k st with
      | P4A.VBits bits => v <> bits
      end
    end.

  Definition interp_store_constraints {bc} (bv: bit_valuation bc) (scs: list (store_constraint bc)) (st: P4A.store) : Prop :=
    List.Forall (fun sc => interp_store_constraint bv sc st) scs.

  Record path_cond bc :=
    { pc_state: P4A.state_type a + bool;
      pc_buf: bit_expr bc;
      pc_buf_len: nat;
      pc_store: list (store_constraint bc); }.
  Arguments pc_state {_} _.
  Arguments pc_buf {_} _.
  Arguments pc_buf_len {_} _.
  Arguments pc_store {_} _.

  Definition config := configuration (P4A.interp a has_extract).

  Definition interp_path_cond (bc: bit_context) (bv: bit_valuation bc) (p: (path_cond bc)) : config -> Prop :=
    fun '(state, store, buf) =>
      state = p.(pc_state) /\
      interp_bit_expr bv p.(pc_buf) buf /\
      List.length buf < p.(pc_buf_len) /\
      interp_store_constraints bv p.(pc_store) store.

  (*
  Print step.
  Print transitions.
  Check (transitions a).

  Definition step {cur_bc} (cur_cond: path_cond cur_bc) : list path_cond :=
    match cur_cond.(pc_state) with
    | inl cur_state =>
      let size := (size a cur_state) in
      let new_bc := BCSnoc size bc in
      let 
    { pc_state: states a + bool;
      pc_buf: bit_expr bc;
      pc_buf_len: nat;
      pc_store: list (store_constraint bc); }.
      
      cond
    | inr true =>
      cond
    | inr false =>
      cond
    end
   *)
End StateCond.
Section StateTemplate.
  Variable (a: P4A.t).
  Variable (has_extract: forall s H, 0 < P4A.size a (exist _ s H)).
  Notation conf := (config a has_extract).

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

  Notation conf1 := (config a1 has_extract1).
  Notation conf2 := (config a2 has_extract2).

  Definition store_rel: Type.
  Admitted.
  
  Definition interp_store_rel (r: store_rel) (c1: conf1) (c2: conf2) : Prop.
  Admitted.

  Record conf_rel :=
    { cr_st1: state_template a1;
      cr_st2: state_template a2;
      cr_rel: store_rel; }.

  Definition interp_path_rel (c: conf_rel) (c1: conf1) (c2: conf2) :=
    interp_state_template _ has_extract1 c.(cr_st1) c1 /\
    interp_state_template _ has_extract2 c.(cr_st2) c2 /\
    interp_store_rel c.(cr_rel) c1 c2.

  Definition chunked_relation :=
    list conf_rel.

  Definition interp_chunked_relation (rel: chunked_relation) :=
    List.map interp_path_rel rel.

End ConfRel.
