Require Import String.
Require Import HAList.
Require Poulet4.P4cub.Envn.
Require Poulet4.P4cub.BigStep.BSUtil.
Require Poulet4.P4automata.P4automaton.
Module P4A := P4automaton.

Module Env := Poulet4.P4cub.Envn.Env.
Module EnvUtil := Poulet4.P4cub.BigStep.BSUtil.EnvUtil.

Inductive hdr_ref: Type :=
| HRVar (var: string)
| HRField (hdr: hdr_ref) (field: string).

Inductive expr :=
| EHdr (h: hdr_ref)
| ELit (bs: list bool).
(* todo: binops, ...? *)

Inductive state_name: Type := 
| SNName (s: string)
| SNStart.

Definition state_ref: Type := state_name + bool.
    
Record sel_case: Type :=
  { sc_val: list bool;
    sc_st: state_ref }.

Inductive transition: Type :=
| TGoto (state: state_ref)
| TSel (cond: hdr_ref) (cases: list sel_case) (default: state_ref).

Inductive op :=
| OpNil
| OpSeq (s1 s2: op)
| OpExtract (width: BinNums.positive) (hdr: hdr_ref)
| OpAsgn (lhs: hdr_ref) (rhs: expr)
| OpBlock (o: op).

Record state: Type :=
  { st_hdr: hdr_ref;
    st_trans: transition }.

Definition t: Type :=
  Env.t state_name state.

Section Interp.
  Variable (a: t).

  Definition state_type :=
    { s: state_name | a s <> None }.
  
  Definition store := EnvUtil.epsilon.
  
  Definition pre_size (state: state_name) : nat.
  Admitted.

  Definition size (state: state_type) : nat.
  Admitted.

  Variable (has_extract: forall s H, 0 < size (exist _ s H)).

  Definition update (state: state_type) (bits: list bool) (st: store) : store.
  Admitted.
  
  Definition transitions (s: state_type) (st: store) : state_type + bool.
  Admitted.

  Lemma cap: forall s, 0 < size s.
  Proof.
    intros.
    destruct s.
    apply has_extract.
  Qed.
  
  Definition interp (a: t) : P4A.p4automaton :=
    {| P4A.store := store;
       P4A.states := state_type;
       P4A.size := size;
       P4A.update := update;
       P4A.transitions := transitions;
       P4A.cap := cap |}.
End Interp.

                    
