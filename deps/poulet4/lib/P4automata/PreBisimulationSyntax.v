Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
From Equations Require Import Equations.

Require Import Poulet4.P4automata.P4automaton.
Require Poulet4.P4automata.PreBisimulation.
Require Poulet4.P4automata.Syntax.
Module P4A := Poulet4.P4automata.Syntax.

Open Scope list_scope.

Section PathCond.
  Variable (a: p4automaton).
  Variable (a_key: Type).
  Variable (a_lookup: store a -> a_key -> list bool).

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
  | SCEq (k: a_key) (v: bit_expr bc)
  | SCNeq (k: a_key) (v: list bool).

  Definition interp_store_constraint {bc} (bv: bit_valuation bc) (sc: store_constraint bc) (st: store a) : Prop :=
    match sc with
    | SCEq _ k v => interp_bit_expr bv v (a_lookup st k)
    | SCNeq _ k v => v <> a_lookup st k
    end.

  Definition interp_store_constraints {bc} (bv: bit_valuation bc) (scs: list (store_constraint bc)) (st: store a) : Prop :=
    List.Forall (fun sc => interp_store_constraint bv sc st) scs.

  Record path_cond bc :=
    { pc_state: states a + bool;
      pc_buf: bit_expr bc;
      pc_buf_len: nat;
      pc_store: list (store_constraint bc); }.
  Arguments pc_state {_} _.
  Arguments pc_buf {_} _.
  Arguments pc_buf_len {_} _.
  Arguments pc_store {_} _.

  Definition interp_path_cond (bc: bit_context) (bv: bit_valuation bc) (p: (path_cond bc)) : configuration a -> Prop :=
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
End PathCond.

Section PathRel.

  Variable (a1: p4automaton).
  Variable (a1_key: Type).
  Variable (a1_lookup: store a1 -> a1_key -> list bool).
  Variable (a2: p4automaton).
  Variable (a2_key: Type).
  Variable (a2_lookup: store a2 -> a2_key -> list bool).

  Record path_rel :=
    { pr_ctx: bit_context;
      pr_pc1: path_cond a1 a1_key pr_ctx;
      pr_pc2: path_cond a2 a2_key pr_ctx; }.
  
  Definition interp_path_rel (p: path_rel) (conf1: configuration a1) (conf2: configuration a2) :=
    exists bv, 
      interp_path_cond a1 a1_key a1_lookup p.(pr_ctx) bv p.(pr_pc1) conf1 /\
      interp_path_cond a2 a2_key a2_lookup p.(pr_ctx) bv p.(pr_pc2) conf2
  .
 
  Definition chunked_relation :=
    list path_rel
  .

  Definition interp_chunked_relation (rel: chunked_relation): PreBisimulation.chunked_relation a1 a2 :=
    List.map interp_path_rel rel.

End PathRel.
